{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Lexer (module Lexer) where

import Text.Parsec hiding (Parsec)

-- import qualified Text.Parsec.Token as Tok
import qualified ParsecToken as Tok

import Control.Monad
import Control.Monad.Except
import Data.Char (isUpper, isAlpha, isLower)

emptyDef :: Tok.GenLanguageDef String st (Except String)
emptyDef = Tok.LanguageDef
    { Tok.commentStart   = ""
    , Tok.commentEnd     = ""
    , Tok.commentLine    = ""
    , Tok.nestedComments = True
    , Tok.identStart     = letter <|> char '_'
    , Tok.identLetter    = alphaNum <|> oneOf "_'"
    , Tok.opStart        = Tok.opLetter emptyDef
    , Tok.opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
    , Tok.reservedOpNames= []
    , Tok.reservedNames  = []
    , Tok.caseSensitive  = True
    }

langDef :: Tok.GenLanguageDef String st (Except String)
langDef = emptyDef
    { Tok.commentStart    = "{-"
    , Tok.commentEnd      = "-}"
    , Tok.commentLine     = "--"
    , Tok.reservedOpNames = ops
    , Tok.reservedNames   = names
    }
  where
    ops = [ "="
          , "->"
          , "=>"
          , "+"
          , "-"
          , "*"
          , "/"
          , "++"
          , "=="
          , ">"
          , "<"
          , "|"
          , "()"
          , "[]"
          , "@"
          , "!"
          ]
    names = [ "fun"
            , "if"
            , "then"
            , "else"
            , "let"
            , "letrec"
            , "in"
            , "data"
            , "effect"
            , "handle"
            , "with"
            , "case"
            , "of"
            , "print"
            , "do"
            ---------------
            , "fst"
            , "snd"
            ---------------
            , "forall"
            , "Int"
            , "Char"
            , "String"
            ---------------
            , "Any"
            , "Abs"
            ]

lexer :: Tok.GenTokenParser String u (Except String)
lexer = Tok.makeTokenParser langDef

type Parsec s u a = ParsecT s u (Except String) a

comma :: Parsec String u ()
comma = void $ Tok.comma lexer

dot :: Parsec String u ()
dot = void $ Tok.dot lexer

colon :: Parsec String u ()
colon = void $ Tok.colon lexer

semi :: Parsec String u ()
semi = void $ Tok.semi lexer

parens :: Parsec String u a -> Parsec String u a
parens = Tok.parens lexer

brackets :: Parsec String u a -> Parsec String u a
brackets = Tok.brackets lexer

braces :: Parsec String u a -> Parsec String u a
braces = Tok.braces lexer

angles :: Parsec String u a -> Parsec String u a
angles = Tok.angles lexer

natural :: Parsec String u Integer
natural = Tok.natural lexer

charLiteral :: Parsec String u Char
charLiteral = Tok.charLiteral lexer

stringLiteral :: Parsec String u String
stringLiteral = Tok.stringLiteral lexer

whiteSpace :: Parsec String u ()
whiteSpace = Tok.whiteSpace lexer

commaSep :: Parsec String u a -> Parsec String u [a]
commaSep = Tok.commaSep lexer

semiSep :: Parsec String u a -> Parsec String u [a]
semiSep = Tok.semiSep lexer

identifier :: Parsec String u String
identifier = Tok.identifier lexer

satiden :: (String -> Bool) -> Parsec String u String
satiden p = try $ do
  x <- identifier
  unless (p x) $ fail "unsatisfied identifier"
  return x

alphaiden :: Parsec String u String
alphaiden = satiden (isAlpha . head)

loweriden :: Parsec String u String
loweriden = satiden (\ (x:_) -> isLower x || x == '_')

upperiden :: Parsec String u String
upperiden = satiden (\ (x:_) -> isUpper x || x == '_')

reserved :: String -> Parsec String u ()
reserved = Tok.reserved lexer

reservedOp :: String -> Parsec String u ()
reservedOp = Tok.reservedOp lexer

arrow :: Parsec String u ()
arrow = reservedOp "->"