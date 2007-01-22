module Parser
    ( memeParse
    )
where

import AST

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language (haskellStyle)
import Text.ParserCombinators.Parsec.Token

type MParser a = GenParser Char () a

memeParse :: SourceName -> String -> AST
memeParse name text =
    case parse parseExpr name text of
        Left  err -> error $ show err
        Right ast -> ast

meme :: LanguageDef st
meme = haskellStyle

memeTok :: TokenParser st
memeTok = makeTokenParser meme

tok :: (TokenParser st -> a) -> a
tok = ($ memeTok)

-- this is to allow type annotations anywhere
parseAST :: MParser AST -> MParser AST
parseAST = id

parseExpr :: MParser AST
parseExpr = choice [ parseLambda
                   , parseApp
                   , parseTerm 
                   ]

parseLambda :: MParser AST
parseLambda = parseAST $ do
    tok symbol "\\"
    parseParam
  where
    parseParam :: MParser AST
    parseParam = do
        name <- tok identifier
        body <- parseParam <|> parseBlock
        return (Lam name body)

    parseBlock :: MParser AST
    parseBlock = tok braces parseExpr

parseApp :: MParser AST
parseApp = parseAST $ do
    parseLeftApp id
  where
    parseLeftApp :: (AST -> AST) -> MParser AST
    parseLeftApp f = do
        term <- parseTerm
        option (f term) $ parseLeftApp (App (f term))

parseTerm :: MParser AST
parseTerm = choice [ parseVar
                   , parseParens
                   ]

parseVar :: MParser AST
parseVar = parseAST $ do
    fmap Var (tok identifier)

parseParens :: MParser AST
parseParens = parseAST $ tok parens parseExpr
