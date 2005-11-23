module Typist.Syntax (
    parseAST,
) where

import Typist.AST
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Language (haskellStyle)

parseAST :: String -> AST
parseAST str = 
    case parse parseProgram "input" str of
        Left err -> error (show err)
        Right ast -> ast


typistDef :: LanguageDef st
typistDef = haskellStyle {
                reservedNames = words "let in"
            }

typistTok :: TokenParser st
typistTok = makeTokenParser typistDef

tok :: (TokenParser st -> a) -> a
tok f = f typistTok


type TParser st a = CharParser st a

ws :: TParser st a -> TParser st a
ws parser = do
    ans <- parser
    tok whiteSpace
    return ans

parseProgram :: TParser st AST
parseProgram = do
    exp <- parseExpression
    eof
    return exp

parseExpression :: TParser st AST
parseExpression = choice [ parseLambda
                         , parseLet
                         , parseApp
                         , parseAtom
                         ]

parseAtom :: TParser st AST
parseAtom = choice [ parseVar
                   , parseLit
                   , parseParens
                   ]

parseParens :: TParser st AST
parseParens = tok parens parseExpression

parseLambda :: TParser st AST
parseLambda = do
    ws $ char '\\'
    parseParam
    where
    parseParam = do
        param <- ws $ tok identifier
        body <- parseParam <|> parseBody
        return $ Lambda { lamParam = param, lamBody = body }
    parseBody = do
        ws $ string "->"
        parseExpression

parseLet :: TParser st AST
parseLet = do
    -- XXX we need mutual recursion
    ws $ tok reserved "let"
    var <- ws $ tok identifier
    ws $ char '='
    exp <- ws $ parseExpression
    ws $ tok reserved "in"
    body <- ws $ parseExpression
    let newdef = App {
            appFun = Var { varName = "fix" },
            appArg = Lambda {
                lamParam = var,
                lamBody  = exp
            }
        }
    let newbody = App {
            appFun = Lambda {
                lamParam = var,
                lamBody = body
            },
            appArg = newdef
        }
    return $ newbody

    

parseApp :: TParser st AST
parseApp = do
    first <- parseAtom
    rest <- parseLeftApp
    return $ rest first
    where
    -- parse right-associatively and return a function
    -- that transforms to a left-associative expression
    parseLeftApp = choice [ do arg <- parseAtom
                               rest <- parseLeftApp
                               return $ (\fun -> rest (App { appFun = fun, appArg = arg }))
                           , return id
                           ] 

parseVar :: TParser st AST
parseVar = do
    var <- ws $ tok identifier
    return $ Var { varName = var }

parseLit :: TParser st AST
parseLit = parseInt

parseInt :: TParser st AST
parseInt = do
    sign <- choice [ char '-' >> return (-1), optional (char '+') >> return 1 ]
    nat <- ws $ tok natural
    return $ Lit { litLit = Int (sign * nat) }
