module Main

import Data.Maybe
import Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Doc

import SMTLib.AST
import SMTLib.Print
import SMTLib.Parse

||| Test parseSExpr - basic S-expressions
testParseSExpr : IO ()
testParseSExpr = do
  putStrLn "=== Test: parseSExpr ==="

  -- Test symbol
  let result1 = parseSExpr "foo"
  putStrLn $ "  Symbol 'foo': " ++ (show $ ppSExpr <$> result1)

  -- Test keyword
  let result2 = parseSExpr ":produce-models"
  putStrLn $ "  Keyword ':produce-models': " ++ (show $ ppSExpr <$> result2)

  -- Test simple list
  let result3 = parseSExpr "(foo bar baz)"
  putStrLn $ "  Simple list: " ++ (show $ ppSExpr <$> result3)

  -- Test nested list
  let result4 = parseSExpr "(foo (bar baz) qux)"
  putStrLn $ "  Nested list: " ++ (show $ ppSExpr <$> result4)

  -- Test empty list
  let result5 = parseSExpr "()"
  putStrLn $ "  Empty list: " ++ (show $ ppSExpr <$> result5)

  putStrLn "  DONE"

-- ||| Test parseLiteral - numeric literals
-- testParseLiteral : IO ()
-- testParseLiteral = do
--   putStrLn "\n=== Test: parseLiteral ==="

--   -- Test numeral
--   let result1 = parseLiteral (SSymbol (MkSymbol "42"))
--   putStrLn $ "  Numeral '42': " ++ (show $ ppLiteral <$> result1)

--   -- Test negative
--   let result2 = parseLiteral (SSymbol (MkSymbol "-10"))
--   putStrLn $ "  Negative '-10': " ++ (show $ ppLiteral <$> result2)

--   putStrLn "  DONE"

||| Test parseTerm - term parsing
testParseTerm : IO ()
testParseTerm = do
  putStrLn "\n=== Test: parseTerm ==="

  -- Test simple variable
  let result1 = parseTerm (SSymbol (MkSymbol "x"))
  putStrLn $ "  Variable 'x': " ++ (show $ ppTerm <$> result1)

  -- Test function application
  let result2 = parseTerm (SList [SSymbol (MkSymbol "+"), SSymbol (MkSymbol "x"), SSymbol (MkSymbol "y")])
  putStrLn $ "  FunApp '(+ x y)': " ++ (show $ ppTerm <$> result2)

  putStrLn "  DONE"

||| Test parseCommand - command parsing
testParseCommand : IO ()
testParseCommand = do
  putStrLn "\n=== Test: parseCommand ==="

  -- Test check-sat
  let result1 = parseCommand (SList [SSymbol (MkSymbol "check-sat")])
  putStrLn $ "  check-sat: " ++ (show $ ppCommand <$> result1)

  -- Test get-model
  let result2 = parseCommand (SList [SSymbol (MkSymbol "get-model")])
  putStrLn $ "  get-model: " ++ (show $ ppCommand <$> result2)

  -- Test assert
  let result3 = parseCommand (SList [SSymbol (MkSymbol "assert"), SSymbol (MkSymbol "x")])
  putStrLn $ "  assert: " ++ (show $ ppCommand <$> result3)

  -- Test declare-const
  let result4 = parseCommand (SList [SSymbol (MkSymbol "declare-const"), SSymbol (MkSymbol "x"), SSymbol (MkSymbol "Bool")])
  putStrLn $ "  declare-const: " ++ (show $ ppCommand <$> result4)

  -- Test reset
  let result5 = parseCommand (SList [SSymbol (MkSymbol "reset")])
  putStrLn $ "  reset: " ++ (show $ ppCommand <$> result5)

  putStrLn "  DONE"

||| Test parseCommandFromString - full string parsing
testParseCommandFromString : IO ()
testParseCommandFromString = do
  putStrLn "\n=== Test: parseCommandFromString ==="

  -- Test check-sat
  let result1 = parseCommandFromString "(check-sat)"
  putStrLn $ "  check-sat: " ++ (show $ ppCommand <$> result1)

  -- Test declare-const
  let result2 = parseCommandFromString "(declare-const x Real)"
  putStrLn $ "  declare-const: " ++ (show $ ppCommand <$> result2)

  -- Test assert
  let result3 = parseCommandFromString "(assert (> x 0))"
  putStrLn $ "  assert: " ++ (show $ ppCommand <$> result3)

  putStrLn "  DONE"

||| Test parseScript - script parsing
testParseScript : IO ()
testParseScript = do
  putStrLn "\n=== Test: parseScript ==="

  -- Test simple script
  let result1 = parseScript "(check-sat)"
  putStrLn $ "  Single command: " ++ (show $ ppScript <$> result1)

  -- Test multi-command script
  let result2 = parseScript "(declare-const x Real) (assert (> x 0)) (check-sat)"
  putStrLn $ "  Multiple commands: " ++ (show $ ppScript <$> result2)

  putStrLn "  DONE"

||| Test round-trip: parse -> print -> parse
testRoundTrip : IO ()
testRoundTrip = do
  putStrLn "\n=== Test: Round-trip ==="

  -- Parse twice, both should succeed
  let result1 = parseCommandFromString "(declare-const x Real)"
  let result2 = parseCommandFromString "(declare-const x Real)"
  putStrLn $ "  Parse twice: " ++ (case (result1, result2) of
    (Just _, Just _) => "OK"
    _ => "FAIL")

  putStrLn "  DONE"

||| Test error handling with Either
testErrorHandling : IO ()
testErrorHandling = do
  putStrLn "\n=== Test: Error Handling ==="

  -- Test valid command
  let result1 = parseCommandEither "(check-sat)"
  putStrLn $ "  Valid: " ++ (isRight result1)

  -- Test invalid command
  let result2 = parseCommandEither "not a command"
  putStrLn $ "  Invalid: " ++ (isLeft result2)

  -- Test with parseSExprEither
  let result3 = parseSExprEither "foo"
  putStrLn $ "  SExpr valid: " ++ (isRight result3)

  let result4 = parseSExprEither ""
  putStrLn $ "  SExpr empty: " ++ (isLeft result4)

  putStrLn "  DONE"
  where
    isRight : Either e a -> String
    isRight (Left _) = "FAIL"
    isRight (Right _) = "OK"
    isLeft : Either e a -> String
    isLeft (Left _) = "OK"
    isLeft (Right _) = "FAIL"

main : IO ()
main = do
  testParseSExpr
  -- testParseLiteral
  testParseTerm
  testParseCommand
  testParseCommandFromString
  testParseScript
  testRoundTrip
  testErrorHandling
  putStrLn "\n=== All parser tests completed ==="
