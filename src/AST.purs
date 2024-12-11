module AST where

import Prelude

import Control.Alt (alt, (<|>))
import Control.Apply (lift2)
import Control.Lazy (defer)
import Control.Monad.Error.Class (catchError)
import Data.Either (Either(..))
import Data.Either.Nested (type (\/))
import Data.Leibniz (type (~), refute)
import Data.List (List, (:))
import Parsing (ParseError, ParseState(..), Parser, Position, fail, getParserT)
import Parsing.Language (haskellStyle)
import Parsing.String (anyTill)
import Parsing.Token (TokenParser, makeTokenParser)

{-

Identifier ::= "a" | "b" | "c" | ...
Literal ::= Int
Operator ::= "+"
Expression ::= Identifier | Literal | Expression Operator Expression
Statement ::= "let" Identifier "=" Expression | Expression

Program ::= "" | Statement ";" Program

-}

class HFunctor :: forall k1 k2. ((k1 -> Type) -> k2 -> Type) -> Constraint
class HFunctor f where
  hmap :: forall g h p. (forall a. g a -> h a) -> f g p -> f h p

data FixH :: forall k. ((k -> Type) -> k -> Type) -> k -> Type
data FixH f p = InH (f (FixH f) p)

roll :: forall f p. f (FixH f) p -> FixH f p
roll = InH

unroll :: forall f p. FixH f p -> f (FixH f) p
unroll (InH x) = x

foldFix :: forall f g p. HFunctor f => (forall q. f g q -> g q) -> FixH f p -> g p
foldFix alg x = alg $ hmap (foldFix alg) (unroll x)

data ProductH :: forall k. ((k -> Type) -> k -> Type) -> ((k -> Type) -> k -> Type) -> (k -> Type) -> k -> Type
data ProductH f g h p = ProductH (f h p) (g h p)

infixr 5 type ProductH as :*:

instance (HFunctor f, HFunctor g) => HFunctor (ProductH f g) where
  hmap f = case _ of
    ProductH x y -> ProductH (hmap f x) (hmap f y)

data CoproductH :: forall k. ((k -> Type) -> k -> Type) -> ((k -> Type) -> k -> Type) -> (k -> Type) -> k -> Type
data CoproductH f g h p = InLH (f h p) | InRH (g h p)

infixr 5 type CoproductH as :+:

instance (HFunctor f, HFunctor g) => HFunctor (CoproductH f g) where
  hmap f = case _ of
    InLH x -> InLH $ hmap f x
    InRH y -> InRH $ hmap f y

-- 現在の分岐を表す Phantom Type
data ExpressionP
data OperatorP
data LiteralP
data IdentifierP
data ProgramP

data ASTF r p
  =
    -- Literal
    IntLitF Int (p ~ LiteralP)

  -- Operator
  | PlusF (p ~ OperatorP)
  | MulF (p ~ OperatorP)

  -- Expression
  | ExpLitF (r LiteralP) (p ~ ExpressionP)
  | ExpOpF (r OperatorP) (r ExpressionP) (r ExpressionP) (p ~ ExpressionP)
  -- Program
  | EmptyF (p ~ ProgramP)
  | SeqF (r ExpressionP) (r ProgramP) (p ~ ProgramP)

instance HFunctor ASTF where
  hmap f = case _ of
    IntLitF n e -> IntLitF n e
    PlusF e -> PlusF e
    MulF e -> MulF e
    ExpLitF lit e -> ExpLitF (f lit) e
    ExpOpF op exp1 exp2 e -> ExpOpF (f op) (f exp1) (f exp2) e
    EmptyF e -> EmptyF e
    SeqF exp prog e -> SeqF (f exp) (f prog) e

type AST = FixH ASTF

data MetadataF :: (Type -> Type) -> Type -> Type
data MetadataF r p = Metadata Position

instance HFunctor MetadataF where
  hmap _ = case _ of
    Metadata pos -> Metadata pos

data ParseErrorF :: (Type -> Type) -> Type -> Type
data ParseErrorF r p = ErrorInExpF ParseError (p ~ ExpressionP)

instance HFunctor ParseErrorF where
  hmap _ = case _ of
    ErrorInExpF e e' -> ErrorInExpF e e'

type AST' = FixH ((ASTF :+: ParseErrorF) :*: MetadataF)

tokenParser :: TokenParser
tokenParser = makeTokenParser haskellStyle

getPosition :: forall s. Parser s Position
getPosition = do
  ParseState _ pos _ <- getParserT
  pure pos

withMeta :: forall p s. Parser s (ASTF AST' p) -> Parser s (AST' p)
withMeta p = do
  pos <- getPosition
  astf <- p
  pure $ InH $ ProductH (InLH astf) (Metadata pos)

withMetaErr :: forall p s. Parser s (ParseErrorF AST' p) -> Parser s (AST' p)
withMetaErr p = do
  pos <- getPosition
  astf <- p
  pure $ InH $ ProductH (InRH astf) (Metadata pos)

parseLiteral :: Parser String (AST' LiteralP)
parseLiteral = withMeta do
  n <- tokenParser.integer
  pure $ IntLitF n identity

parseOperator :: Parser String (AST' OperatorP)
parseOperator = withMeta do
  op <- tokenParser.operator
  case op of
    "+" -> pure $ PlusF identity
    "*" -> pure $ MulF identity
    unOp -> fail $ "Unknown operator: " <> unOp

parseExpLit :: Parser String (AST' ExpressionP)
parseExpLit = withMeta do
  lit <- parseLiteral
  pure $ ExpLitF lit identity

parseExpression :: Parser String (AST' ExpressionP)
parseExpression = do
  exp <- parseExpLit <|> tokenParser.parens (defer $ \_ -> parseExpression)
  alt
    ( withMeta do
        op <- parseOperator
        exp' <- parseExpression
        pure $ ExpOpF op exp exp' identity
    )
    do
      pure exp

parseProgram :: Parser String (AST' ProgramP)
parseProgram = withMeta do
  alt
    do
      stmt <- parseExpression
      void $ tokenParser.semi
      prog <- parseProgram
      pure $ SeqF stmt prog identity

    do
      pure $ EmptyF identity

skipToSemi :: Parser String Unit
skipToSemi = void $ anyTill (tokenParser.semi)

parseProgramWithErr :: Parser String (AST' ProgramP)
parseProgramWithErr = withMeta do
  alt
    do
      stmt <- catchError
        ( do
            stmt <- parseExpression
            void $ tokenParser.semi
            pure stmt
        )
        \e -> do
          skipToSemi
          withMetaErr $ pure $ ErrorInExpF e identity
      prog <- parseProgramWithErr
      pure $ SeqF stmt prog identity

    do
      pure $ EmptyF identity

data Op = Plus | Mul
data Semantics p
  = IntLitS Int (p ~ LiteralP)
  | OpS Op (p ~ OperatorP)
  | ExpS (String \/ Int) (p ~ ExpressionP)
  | ProgramS (List (String \/ Int)) (p ~ ProgramP)

programHandler :: forall p. ((ASTF :+: ParseErrorF) :*: MetadataF) Semantics p -> Semantics p
programHandler = case _ of
  ProductH astOrErr (Metadata pos) -> case astOrErr of
    InLH ast -> case ast of
      IntLitF n e -> IntLitS n e
      PlusF e -> OpS Plus e
      MulF e -> OpS Mul e
      ExpLitF lit e -> ExpS (Right $ unIntLit lit) e
      ExpOpF op exp1 exp2 e -> case unOperator op of
        Plus -> ExpS (lift2 (+) (unExp exp1) (unExp exp2)) e
        Mul -> ExpS (lift2 (*) (unExp exp1) (unExp exp2)) e
      EmptyF e -> ProgramS mempty e
      SeqF exp prog e ->
        ( ProgramS $ unExp exp : unProgram prog
        ) e
    InRH err -> case err of
      ErrorInExpF _ e' -> ExpS (Left $ "Error in expression " <> show pos) e'

interpretProgram :: forall p. AST' p -> Semantics p
interpretProgram ast' = foldFix programHandler ast'

runProgram :: AST' ProgramP -> List (String \/ Int)
runProgram ast = unProgram (interpretProgram ast)

unIntLit :: Semantics LiteralP -> Int
unIntLit = case _ of
  IntLitS n _ -> n
  OpS _ e -> refute e
  ExpS _ e -> refute e
  ProgramS _ e -> refute e

unExp :: Semantics ExpressionP -> String \/ Int
unExp = case _ of
  IntLitS _ e -> refute e
  OpS _ e -> refute e
  ExpS f _ -> f
  ProgramS _ e -> refute e

unOperator :: Semantics OperatorP -> Op
unOperator = case _ of
  IntLitS _ e -> refute e
  OpS op _ -> op
  ExpS _ e -> refute e
  ProgramS _ e -> refute e

unProgram :: Semantics ProgramP -> List (String \/ Int)
unProgram = case _ of
  IntLitS _ e -> refute e
  OpS _ e -> refute e
  ExpS _ e -> refute e
  ProgramS f _ -> f
