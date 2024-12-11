module Main where

import Prelude

import AST (parseProgramWithErr, runProgram)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Effect (Effect)
import Effect.Console (log)
import Parsing (runParser)

main :: Effect Unit
main = do
  case runParser "1 + 2; 2 * (3 + 4); 2 * 3; " parseProgramWithErr of
    Left err -> log $ "Parse Error: " <> show err
    Right ast -> for_ (runProgram ast) (log <<< show)

  log ""

  case runParser "1 + 2; 2 ** (3 + 4); 2 * 3; " parseProgramWithErr of
    Left err -> log $ "Parse Error: " <> show err
    Right ast -> for_ (runProgram ast) (log <<< show)
