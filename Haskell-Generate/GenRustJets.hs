{-# LANGUAGE OverloadedStrings #-}
module GenRustJets where

import Data.Char (isAlphaNum, isDigit, isUpper, toLower, toUpper)
import Data.Function (on)
import Data.Functor.Fixedpoint (Fix(..))
import Data.List (groupBy, intercalate, sortBy)
import Data.List.Split (chunksOf, condense, dropInitBlank, keepDelimsL, split, whenElt)
import qualified Data.Map as Map
import Numeric (showHex)
import Prettyprinter ( Doc, (<+>), comma, fillSep, line, nest, pretty, punctuate, semi, vsep
                     , SimpleDocStream, LayoutOptions(..), PageWidth(..), defaultLayoutOptions, layoutPretty
                     )
import Prettyprinter.Render.Text (renderIO)
import System.IO (IOMode(WriteMode), withFile)

import qualified Simplicity.Bitcoin.Jets as Bitcoin
import Simplicity.CoreJets
import Simplicity.Digest
import qualified Simplicity.Elements.Jets as Elements
import Simplicity.MerkleRoot
import Simplicity.Serialization
import Simplicity.Ty

data JetData x y = JetData { jetName :: String
                           , jetIdentity :: IdentityRoot x y
                           }

sortJetName = sortBy (compare `on` name)
 where
  name (SomeArrow j) = jetName j

mkName :: Show a => a -> String
mkName = filter isAlphaNum . last . words . show

coreJetData :: (TyC x, TyC y) => CoreJet x y -> JetData x y
coreJetData jet = JetData { jetName = mkName jet
                          , jetIdentity = specification jet
                          }

elementsJetData :: (TyC x, TyC y) => Elements.JetType x y -> JetData x y
elementsJetData jet = JetData { jetName = mkName jet
                              , jetIdentity = Elements.specification jet
                              }

bitcoinJetData :: (TyC x, TyC y) => Bitcoin.JetType x y -> JetData x y
bitcoinJetData jet = JetData { jetName = mkName jet
                             , jetIdentity = Bitcoin.specification jet
                             }

data Module = Module { moduleName :: String
                     , moduleJets :: [SomeArrow JetData]
                     }

coreModule :: Module
coreModule = Module "Core" (sortJetName [SomeArrow (coreJetData jet) | (SomeArrow jet) <- Map.elems coreJetMap])

elementsModule :: Module
elementsModule = Module "Elements" (sortJetName [SomeArrow (elementsJetData jet) | (SomeArrow jet) <- Map.elems Elements.jetMap])

bitcoinModule :: Module
bitcoinModule = Module "Bitcoin" (sortJetName [SomeArrow (bitcoinJetData jet) | (SomeArrow jet) <- Map.elems Bitcoin.jetMap])

data CompactTy = CTyOne
               | CTyWord Int
               | CTyMaybe CompactTy
               | CTySum CompactTy CompactTy
               | CTyProd CompactTy CompactTy
     deriving (Eq, Ord)

snakeCase :: String -> String
snakeCase str = intercalate "_" . groupSingles $ (split . keepDelimsL . dropInitBlank . whenElt) isUpper =<< splitDigit
 where
  splitDigit = (split . condense . whenElt) isDigit $ str
  groupSingles = map concat . groupBy singles
   where
    singles x y = null (tail x) && null (tail y)

upperSnakeCase :: String -> String
upperSnakeCase = map toUpper . snakeCase

lowerSnakeCase :: String -> String
lowerSnakeCase = map toLower . snakeCase

compactTy :: Ty -> CompactTy
compactTy = memoCataTy go
 where
  go One = CTyOne
  go (Sum CTyOne CTyOne) = CTyWord 1
  go (Sum CTyOne y) = CTyMaybe y
  go (Sum x y) = CTySum x y
  go (Prod (CTyWord wx) (CTyWord wy)) | wx == wy = CTyWord (wx + wy)
  go (Prod x y) = CTyProd x y

compactRustName :: CompactTy -> ShowS
compactRustName s = showString "TypeName(b\"" . go s . showString "\")"
 where
  go CTyOne = showString "1"
  go (CTyWord 1) = showString "2"
  go (CTyWord 32) = showString "i"
  go (CTyWord 64) = showString "l"
  go (CTyWord 256) = showString "h"
  go (CTyWord n) | even n = let rec = go (CTyWord (n `div` 2)) in showString "*" . rec . rec
  go (CTyMaybe x) = showString "+1" . go x
  go (CTySum x y) = showString "+" . go x . go y
  go (CTyProd x y) = showString "*" . go x . go y

showRustHash :: Hash256 -> Doc a
showRustHash h = fillSep $ ((<> comma) . format <$> chunksOf 2 str_h)
 where
  format x = pretty $ "0x" ++ x
  str_h = padding ++ text
   where
    padding = replicate (64 - length text) '0'
    text = showHex (integerHash256 h) ""

rustJetNode :: (TyC x, TyC y) => String -> JetData x y -> Doc a
rustJetNode modname jet = vsep $
  [ nest 4 (vsep ("pub const" <+> pretty (upperSnakeCase name) <> pretty (": JetNode<" ++ modname ++ "> = JetNode {") :
      map (<>comma)
      [ "name:" <+> pretty (modname ++ "JetName::" ++ name)
      , "cmr:" <+> nest 4 (vsep
        [ "Cmr(Midstate(["
        , showRustHash (identityRoot (jetIdentity jet))
        ]) <> line <> "]))"
      , "source_ty:" <+> pretty (compactRustName (compactTy (unreflect tyx)) "")
      , "target_ty:" <+> pretty (compactRustName (compactTy (unreflect tyy)) "")
      ]))
  , "};"
  ]
 where
  name = jetName jet
  (tyx, tyy) = reifyArrow jet

rustJetNodes :: Module -> Doc a
rustJetNodes mod = vsep $ punctuate line [rustJetNode (moduleName mod) jet | (SomeArrow jet) <- moduleJets mod]

rustJetEnum :: Module -> Doc a
rustJetEnum mod = vsep
 [ pretty $ "/// Identifiers of all possible " ++ moduleName mod ++ " jets"
 , "#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]"
 , nest 4 (vsep (pretty ("pub enum " ++ moduleName mod ++ "JetName {") 
   : [pretty (jetName jet) <> comma | (SomeArrow jet) <- moduleJets mod]))
 , "}"
 ]

rustHeader :: Doc a
rustHeader = "/* This file has been automatically generated. */"

rustImports :: Module -> Doc a
rustImports mod = vsep (map (<> semi)
  [ pretty ("use crate::jet::application::" ++ moduleName mod)
  , "use crate::jet::type_name::TypeName"
  , "use crate::jet::JetNode"
  , "use crate::merkle::cmr::Cmr"
  , "use bitcoin_hashes::sha256::Midstate"
  ])

rustJetDoc :: Module -> SimpleDocStream a
rustJetDoc mod = layoutPretty layoutOptions $ vsep (map (<> line)
  [ rustHeader
  , rustImports mod
  , rustJetEnum mod
  , rustJetNodes mod
  ])
 where
  layoutOptions = LayoutOptions { layoutPageWidth = AvailablePerLine 100 1 }

rustCoreJetDoc :: SimpleDocStream a
rustCoreJetDoc = rustJetDoc coreModule

rustElementsJetDoc :: SimpleDocStream a
rustElementsJetDoc = rustJetDoc elementsModule

rustBitcoinJetDoc :: SimpleDocStream a
rustBitcoinJetDoc = rustJetDoc bitcoinModule

renderFile name doc = withFile name WriteMode (\h -> renderIO h doc)

main = do
  renderFile "core.rs" rustCoreJetDoc
  renderFile "elements.rs" rustElementsJetDoc
  renderFile "bitcoin.rs" rustBitcoinJetDoc
