-- Falta Frame de Let e If

module BAE.Dynamic where

import Data.List
import BAE.Sintax as Sintax
import BAE.Type as Type

type Pending = ()
data Frame = FnF Identifier Pending
           | AddFL Pending Expr
           | AddFR Expr Pending
           | MulFL Pending Expr
           | MulFR Expr Pending
           | SuccF Pending
           | PredF Pending
           | NotF Pending
           | AndFL Pending Expr
           | AndFR Expr Pending
           | OrFL Pending Expr
           | OrFR Expr Pending
           | LtFL Pending Expr
           | LtFR Expr Pending
           | GtFL Pending Expr
           | GtFR Expr Pending
           | EqFL Pending Expr
           | EqFR Expr Pending
           | IfF Pending Expr Expr
           | Let
           | Fn
           | AppFL Pending Expr
           | AppFR Expr Pending
           | Alloc Pending
           | Deref Pending
           | AssigFL Pending Expr
           | AssigFR Expr Pending
           | SeqFL Pending Expr
           | SeqFR Expr Pending
           | WhileFL Pending Expr
           | WhileFR Expr Pending

instance Show Frame where
    show e = case e of
        (AddFL p e2) -> "Sum(-, " ++ (show e2) ++ ")"
        (AddFR e1 p) -> "Sum(" ++ (show e1) ++"-)"
        (MulFL p e2) -> "Mul(-, " ++ (show e2) ++ ")"
        (MulFR e1 p) -> "Mul(" ++ (show e1) ++"-)"
        (Succ n) -> "Succ(-)"
        (Pred n) -> "Pred(-)"
        (Not e) -> "Not(-)"
        (AndFL p e2) -> "And(-, " ++ (show e2) ++ ")"
        (AndFR e1 p) -> "And(" ++ (show e1) ++"-)"
        (OrFL p e2) -> "Or(-, " ++ (show e2) ++ ")"
        (OrFR e1 p) -> "Or(" ++ (show e1) ++"-)"
        (LtFL p e2) -> "Lt(-, " ++ (show e2) ++ ")"
        (LtFR e1 p) -> "Lt(" ++ (show e1) ++"-)"
        (GtFL p e2) -> "Gt(-, " ++ (show e2) ++ ")"
        (GtFR e1 p) -> "Gt(" ++ (show e1) ++"-)"
        (EqFL p e2) -> "Eq(-, " ++ (show e2) ++ ")"
        (EqFR e1 p) -> "Eq(" ++ (show e1) ++"-)"
        (If e1 e2 e3) -> "If(-," ++ (show e2) ++ ", " ++ (show e3) ++ ")"
        (Let v e1 e2) -> "Let(" ++ (show e1) ++ ", " ++ (show v) ++ "." ++ (show e2) ++ ")"
        (Fn v e) -> "\\"++v++"->"++(show e)
        (AppFL p e2) -> "App(-, " ++ (show e2) ++ ")"
        (AppFR e1 p) -> "App(" ++ (show e1) ++"-)"
        (L n) -> "L "++ (show n)
        Void -> "Void"
        (Alloc n) -> "Alloc(-)"
        (Deref e) -> "Deref(-)"
        (AssigFL p e2) -> "Assig(-, " ++ (show e2) ++ ")"
        (AssigFR e1 p) -> "Assig(" ++ (show e1) ++"-)"
        (SeqFL p e2) -> "Seq(-, " ++ (show e2) ++ ")"
        (SeqFR e1 p) -> "Seq(" ++ (show e1) ++"-)"
        (WhileFL p e2) -> "While(-, " ++ (show e2) ++ ")"
        (WhileFR e1 p) -> "While(" ++ (show e1) ++"-)"


-- Para alphaEq vamos a decir que los marcos son iguales.




esValor :: Expr -> Bool
esValor (V i) = True
esValor (I n) = True
esValor (B b) = True
esValor (Fn v e) = (esValor e)





































normal :: Expr -> Bool
normal fix = false

locked :: Expr -> Bool
locked (Fix x e) = Falses
locked (Let e1 e2) = locked e1

evale :: Expr -> alphaExpr
        (Fix x e) = (Fix x e)




-- A la derecha hay que satisfacer algo, a la izquierda es el contexto.
