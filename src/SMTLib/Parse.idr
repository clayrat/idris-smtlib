module SMTLib.Parse

import Data.List
import Data.String
import SMTLib.AST

%default total

-- ============================================================================
-- Error Handling
-- ============================================================================

||| Parse error with message
public export
record ParseError where
  constructor MkParseError
  message : String

export
Show ParseError where
  show (MkParseError msg) = "Parse error: \{msg}"

||| Convert a Maybe to Either with a simple error message
toEither : String -> Maybe a -> Either ParseError a
toEither msg Nothing = Left (MkParseError msg)
toEither _ (Just a) = Right a

-- ============================================================================
-- Simple String-based S-Expression Parser
-- ============================================================================

||| Check if character is valid symbol character
isSymbolChar : Char -> Bool
isSymbolChar c = isAlphaNum c || c == '~' || c == '!' || c == '@'
              || c == '#' || c == '$' || c == '%' || c == '^' || c == '&'
              || c == '*' || c == '_' || c == '-' || c == '+' || c == '='
              || c == '<' || c == '>' || c == '.' || c == '?' || c == '/'

||| Check if character is a digit
isDigitChar : Char -> Bool
isDigitChar c = c >= '0' && c <= '9'

||| Drop leading whitespace
dropSpaces : String -> String
dropSpaces s = pack $ dropWhile isSpace (unpack s)

||| Read a symbol from string
readSymbol : String -> Maybe (String, String)
readSymbol s = case unpack s of
  [] => Nothing
  (c :: cs) => if isSymbolChar c
    then let (sym, rest) = span isSymbolChar (c :: cs)
         in Just (pack sym, pack rest)
    else Nothing

||| Read a keyword (starts with colon)
readKeyword : String -> Maybe (String, String)
readKeyword s = case unpack s of
  (':' :: cs) => case readSymbol (pack cs) of
    Just (kw, rest) => Just (":" ++ kw, rest)
    Nothing => Nothing
  _ => Nothing

||| Read digits
readDigits : String -> Maybe (String, String)
readDigits s = case unpack s of
  [] => Nothing
  (c :: cs) => if isDigitChar c
    then let (ds, rest) = span isDigitChar (c :: cs)
         in Just (pack ds, pack rest)
    else Nothing

mutual
  ||| Parse an S-Expression from string
  ||| Returns (parsed result, remaining string)
  export
  parseSExpr' : String -> Maybe (SExpr, String)
  parseSExpr' s = let s' = dropSpaces s in
    case unpack s' of
      [] => Nothing
      ('(' :: rest) => case assert_total (parseSList' (pack rest)) of
        Just (exprs, rest') => let s'' = dropSpaces rest' in
          case unpack s'' of
            (')' :: rs) => Just (SList exprs, pack rs)
            _ => Nothing
        Nothing => Nothing
      (':' :: _) => case readKeyword s' of
        Just (kw, rest) => Just (SKeyword kw, rest)
        Nothing => Nothing
      _ => case readSymbol s' of
        Just (sym, rest) => Just (SSymbol (MkSymbol sym), rest)
        Nothing => Nothing

  ||| Parse a list of S-Expressions
  parseSList' : String -> Maybe (List SExpr, String)
  parseSList' s = let s' = dropSpaces s in
    case unpack s' of
      [] => Just ([], "")
      (')' :: _) => Just ([], s')
      _ => case parseSExpr' s' of
        Nothing => Just ([], s')
        Just (e, rest) => case assert_total (parseSList' rest) of
          Nothing => Just ([e], rest)
          Just (es, rest2) => Just (e :: es, rest2)

||| Parse an S-Expression (full string, fail if not all consumed)
export
parseSExpr : String -> Maybe SExpr
parseSExpr s = case parseSExpr' s of
  Just (e, rest) => if all isSpace (unpack (dropSpaces rest)) then Just e else Nothing
  Nothing => Nothing

||| Parse a list of S-Expressions
export
parseSList : String -> Maybe (List SExpr)
parseSList s = case parseSList' s of
  Just (es, rest) => if all isSpace (unpack (dropSpaces rest)) then Just es else Nothing
  Nothing => Nothing

-- ============================================================================
-- AST Parsers (from S-Expressions)
-- ============================================================================

-- ||| Parse a Literal from S-Expression
-- export
-- parseLiteral : SExpr -> Maybe Literal
-- parseLiteral (SList _) = Nothing
-- parseLiteral (SKeyword _) = Nothing
-- parseLiteral (SSymbol (MkSymbol s)) = case unpack s of
--   ('-' :: cs) => case readDigits (pack cs) of
--     Just (ds, "") => Just (Numeral (negate (cast ds)))
--     _ => Nothing
--   _ => case readDigits s of
--     Just (ds, "") => Just (Numeral (cast ds))
--     _ => Nothing

||| Get symbol name from SExpr
getSymbol : SExpr -> Maybe String
getSymbol (SSymbol (MkSymbol n)) = Just n
getSymbol _ = Nothing

||| Parse an Identifier from S-Expression
export
parseIdentifier : SExpr -> Maybe Identifier
parseIdentifier (SSymbol (MkSymbol n)) = Just (MkIdentifier (MkSymbol n) [])
parseIdentifier (SList (SSymbol (MkSymbol n) :: indices)) =
  Just (MkIdentifier (MkSymbol n) indices)
parseIdentifier _ = Nothing

||| Parse a Sort from S-Expression
export
parseSort : SExpr -> Maybe Sort
parseSort (SSymbol (MkSymbol n)) = Just (MkSort (MkIdentifier (MkSymbol n) []) [])
parseSort (SList (SSymbol (MkSymbol n) :: args)) = do
  args' <- traverse (\x => assert_total (parseSort x)) args
  Just (MkSort (MkIdentifier (MkSymbol n) []) args')
parseSort _ = Nothing

||| Parse a SortedVar from S-Expression
export
parseSortedVar : SExpr -> Maybe SortedVar
parseSortedVar (SList [SSymbol (MkSymbol name), sort]) = do
  sort' <- parseSort sort
  Just (MkSortedVar (MkSymbol name) sort')
parseSortedVar _ = Nothing

||| Parse a QIdentifier from S-Expression
export
parseQIdentifier : SExpr -> Maybe QIdentifier
parseQIdentifier (SSymbol (MkSymbol n)) =
  Just (MkQIdentifier (MkIdentifier (MkSymbol n) []) Nothing)
parseQIdentifier (SList [SSymbol (MkSymbol "as"), SSymbol (MkSymbol n), sort]) = do
  sort' <- parseSort sort
  Just (MkQIdentifier (MkIdentifier (MkSymbol n) []) (Just sort'))
parseQIdentifier _ = Nothing

mutual
  ||| Parse a Term from S-Expression
  export
  parseTerm : SExpr -> Maybe Term
  parseTerm (SList (SSymbol (MkSymbol "let") :: rest)) = do
    (vars, body) <- parseLetBody rest
    Just (Let vars [] body)
  parseTerm (SList (SSymbol (MkSymbol "forall") :: rest)) = do
    (vars, body) <- parseQuantifierBody rest
    Just (Forall vars [] body)
  parseTerm (SList (SSymbol (MkSymbol "exists") :: rest)) = do
    (vars, body) <- parseQuantifierBody rest
    Just (Exists vars [] body)
  parseTerm (SList (func :: args)) = do
    func' <- parseQIdentifier func
    args' <- traverse (\x => assert_total (parseTerm x)) args
    Just (FunApp func' args')
  parseTerm (SSymbol s) = Just (QI (MkQIdentifier (MkIdentifier s []) Nothing))
  parseTerm (SKeyword _) = Nothing
  parseTerm (SList []) = Nothing
  parseTerm (SLiteral l) = pure $ Lit l

  ||| Parse let bindings from rest of S-Expression
  parseLetBody : List SExpr -> Maybe (VarBinding, Term)
  parseLetBody [SList [var, val], body] = do
    var' <- getSymbol var
    val' <- parseTerm val
    body' <- parseTerm body
    Just (MkVarBinding (MkSymbol var') val', body')
  parseLetBody (SList [var, val] :: rest) = do
    var' <- getSymbol var
    val' <- parseTerm val
    case rest of
      [] => Just (MkVarBinding (MkSymbol var') val', Lit (Numeral 0)) -- TODO
      (body :: _) => do
        body' <- parseTerm body
        Just (MkVarBinding (MkSymbol var') val', body')
  parseLetBody _ = Nothing

  ||| Parse quantifier (forall/exists) bindings
  parseQuantifierBody : List SExpr -> Maybe (SortedVar, Term)
  parseQuantifierBody [SList [var, sort], body] = do
    var' <- getSymbol var
    sort' <- parseSort sort
    body' <- parseTerm body
    Just (MkSortedVar (MkSymbol var') sort', body')
  parseQuantifierBody _ = Nothing

||| Parse a FunDef from S-Expression
export
parseFunDef : SExpr -> Maybe FunDef
parseFunDef (SList [SSymbol (MkSymbol name), SList vars, retSort, body]) = do
  vars' <- traverse parseSortedVar vars
  sort' <- parseSort retSort
  body' <- parseTerm body
  Just (MkFunDef (MkSymbol name) vars' sort' body')
parseFunDef _ = Nothing

||| Parse a Command from S-Expression
export
parseCommand : SExpr -> Maybe Command
parseCommand (SList (SSymbol (MkSymbol "echo") :: [SKeyword str])) = Just (Echo str)
parseCommand (SList (SSymbol (MkSymbol "declare-const") :: SSymbol (MkSymbol name) :: [sort])) = do
  sort' <- parseSort sort
  Just (DeclareConst (MkSymbol name) sort')
parseCommand (SList (SSymbol (MkSymbol "declare-fun") :: SSymbol (MkSymbol name) :: [SList args, ret])) = do
  args' <- traverse parseSort args
  ret' <- parseSort ret
  Just (DeclareFun (MkSymbol name) args' ret')
parseCommand (SList (SSymbol (MkSymbol "declare-sort") :: SSymbol (MkSymbol name) :: rest)) =
  Just (DeclareSort (MkSymbol name) Nothing) -- TODO arity
parseCommand (SList (SSymbol (MkSymbol "define-fun") :: [fundef])) = do
  fundef' <- parseFunDef fundef
  Just (DefineFun fundef')
parseCommand (SList (SSymbol (MkSymbol "assert") :: [term])) = do
  term' <- parseTerm term
  Just (Assert term')
parseCommand (SList [SSymbol (MkSymbol "check-sat")]) = Just CheckSat
parseCommand (SList [SSymbol (MkSymbol "get-model")]) = Just GetModel
parseCommand (SList (SSymbol (MkSymbol "push") :: rest)) = Just (Push Nothing)
parseCommand (SList (SSymbol (MkSymbol "pop") :: rest)) = Just (Pop Nothing)
parseCommand (SList (SSymbol (MkSymbol "reset") :: _)) = Just Reset
parseCommand _ = Nothing

-- ============================================================================
-- Command and Script Parsers (String -> Command)
-- ============================================================================

||| Parse a Command from string
||| This combines parsing the string to S-Expression and then to Command
export
parseCommandFromString : String -> Maybe Command
parseCommandFromString s = do
  sexpr <- parseSExpr s
  parseCommand sexpr

||| Parse remaining commands from string (for incremental parsing)
parseCommands' : String -> Maybe (List Command, String)
parseCommands' s = let s' = dropSpaces s in
  case unpack s' of
    [] => Just ([], "")
    _ => case parseSExpr' s' of
      Nothing => Just ([], s')
      Just (sexpr, rest) => case parseCommand sexpr of
        Nothing => Just ([], s')
        Just cmd => case assert_total (parseCommands' rest) of
          Nothing => Just ([cmd], rest)
          Just (cmds, rest2) => Just (cmd :: cmds, rest2)

||| Parse a script (list of commands) from string
export
parseScript : String -> Maybe (List Command)
parseScript s = case parseCommands' s of
  Just (cmds, rest) => if all isSpace (unpack (dropSpaces rest)) then Just cmds else Nothing
  Nothing => Nothing

-- ============================================================================
-- Error Handling - Either-based Parsing
-- ============================================================================

||| Parse an S-Expression with error information
export
parseSExprEither : String -> Either ParseError SExpr
parseSExprEither s = toEither "Failed to parse S-Expression" (parseSExpr s)

||| Parse a Command with error information
export
parseCommandEither : String -> Either ParseError Command
parseCommandEither s = toEither "Failed to parse command" (parseCommandFromString s)

||| Parse a script with error information
export
parseScriptEither : String -> Either ParseError (List Command)
parseScriptEither s = toEither "Failed to parse script" (parseScript s)