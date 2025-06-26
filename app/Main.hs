module Main (main) where

import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Data.Time
import Prelude hiding (seq, abs)
import System.Environment
import Parser
import BwdFwd
import Syntax
import Typer
import Helper
import Interpreter
import Printer

dash :: Int -> String
dash n = replicate n '-'

alignName :: String -> String
alignName s = let len = length s in
  if len < 8 then s ++ "\t"
  else if len < 12 then s ++ replicate (12-len) ' '
  else if len < 14 then s ++ replicate (14-len) ' '
  else if len < 16 then s ++ "\t"
  else s ++ " "

runFile :: Bool -> String -> IO ()
runFile debug fileName = do
  file <- readFile fileName
  startParsing <- getCurrentTime
  case runps parseGlobal file of
      Left err          -> putStr "❌ Parse failed: " >> putStrLn err
      Right (Left err)  -> putStr "❌ Parse failed: " >> print err -- parsec error
      Right (Right ctx) -> do
        endParsing <- getCurrentTime
        putStrLn $ "🐶 Parse succeeds in " ++ show (diffUTCTime endParsing startParsing)
        when debug $ do
          putStrLn "Printing the Context:"
          putStrLn $ dash 64
          mapM_ print ctx
        startTyping <- getCurrentTime
        let typcheck = fmap (snd . fst) . runContextual Nil $ typCtx ctx
        case typcheck of
          Left err -> putStrLn "❌ Type checking failed:" >> putStrLn err
          Right list -> do
            endTyping <- getCurrentTime
            putStrLn $ "🐱 Type checking succeeds in " ++ show (diffUTCTime endTyping startTyping)
            mapM_ (\ (name, ty) -> do
                if debug then putStrLn name >> putStrLn (show ty)
                else putStrLn $ alignName name ++ ": " ++ showType ty
              ) list
            startEval <- getCurrentTime
            let result = runContextual Nil $ do
                  erasedCtx <- eraseCtx ctx
                  ((evaluatedCtx, results), _outputCtx) <- runWriterT $ evalCtx erasedCtx
                  put evaluatedCtx
                  let ran = App (var "main") (Cons "unit" [])
                  (res, output) <- runWriterT $ eval ran
                  return (res, results, output)
            case result of
              Left err -> putStr "❌ Evaluation failed: " >> putStrLn err
              Right ((tm, _, output), _) -> do
                endEval <- getCurrentTime
                putStrLn $ "🐰 Evaluation succeeds in " ++ show (diffUTCTime endEval startEval)
                -- mapM_ (\ (name, res) -> putStrLn $ alignName name ++ " = " ++ showValue res) tms
                when (output /= "") $ putStrLn output
                putStrLn (showValue tm) -- print tm

main :: IO ()
main = do
  args <- getArgs
  case args of
    [sourceFileName] -> runFile False sourceFileName
    _ -> putStrLn "Please provide a program file."