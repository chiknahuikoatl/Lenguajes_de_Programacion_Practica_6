module Static where

    import qualified Data.List as List
    import qualified BAE.Semantic as Sem
    import qualified BAE.Sintax
    import qualified BAE.Unifier

    type Identifier = Int
    type Substitution = [(Identifier, Type)]
    type Ctxt = [(Lc.Identifier, Type)]
    type Constraint = [(Type, Type)]
    infix :->

    data Type = T Identifier
                Type :-> Type deriving (Show, Eq)

    vars :: Type -> [Identifier]
    vars (T t) = [t]
    vars (t1 :-> t2) = (List.union (vars t1) (vars t2))

    subst :: Ctxt -> Substitution -> Ctxt
    subst [] _ = []
    subst (x,t):xs s = ((x,(subst t s)):(subst xs s))

    comp :: Substitution -> Substitution -> Substitution
    comp s1 s2 = (List.Union [(x, (subst t2) | (x,t) <- s1]
                    [(x,t) | (x, t) <-,List.notElem x [y | (y,t) <-s1]])

    substCtxt :: Ctxt -> Substitution -> Ctxt
    substCtxt [] _ = []
    substCtxt ((x, t):cs) s = (s, subst t s):(substCtxt cs s)

    find :: Sem.Identifier -> Ctxt -> Maybe Type
    find _ [] = Nothing
    find x ((s,t):c) = if (x == s) then (Just t) else (find x c)

    fresh' :: Type -> [Type] -> Type
    fresh' (T n) vars = if List.elem (T n) vars then
                            fresh' (T (suc n)) vars
                        else (T n)

    fresh :: [Type] -> Type
    fresh vars = (fresh' (T 0) vars)

    clean :: [Type] -> [Int]
    clean ((T n):xs) = [n]++(clean xs)


    infer' :: ([Type], Sem.Expr) -> ([Type], Ctxt, Type, Constraint)
    infer' (v, (Sem.I i)) = let n = fresh v
                                tl = List.union v, [n]
                            in (tl, [(i,n)], n, [])
    infer' (v, (Sem.B b)) = let f = fresh v
                                tl = List.union i, [f]
                            in (tl, [(b, f)], f, [])
    infer' (v, (Sem.V x)) = let t = fresh v
                                    nv' = List.union v [t]
                                in (nv',[(x,t)], t, [])
    infer' (v, (Sem.Add e1 e2)) = let (v1, g1, t1, r1) = infer' (v, e1)
                                  (v2, g2, t2, r2) = infer' (v, e2)
                                  s = [(s1,s2)|(x,s1) <- g1, (y,s2) <- g2, x==y]
                                  z = fresh s
                                  nv' = List.union s [z]
                              in
                                (nv', List.union g1 g2, z, List.union (r1
                                    (List.union r2 s))
    infer' (v, (Sem.Mul e1 e2)) = let (v1, g1, t1, r1) = infer' (v, e1)
                                  (v2, g2, t2, r2) = infer' (v, e2)
                                  s = [(s1,s2)|(x,s1) <- g1, (y,s2) <- g2, x==y]
                                  z = fresh s
                                  nv' = List.union s [z]
                              in
                                (nv', List.union g1 g2, z, List.union (r1
                                    (List.union r2 s))
    infer' (v, (Sem.Suc e)) = let (v, g, t, r) = infer' (v, e)
                                  z = fresh g
                                  nv' = List.union g [z]
                              in
                                (nv', g, z, r)
    infer' (v, (Sem.Pred e)) = let (v, g, t, r) = infer' (v, e)
                                  z = fresh g
                                  nv' = List.union g [z]
                              in
                                (nv', g, z, r)
    infer' (v, (Sem.Not e)) = let (v, g, t, r) = infer' (v, e)
                                  z = fresh g
                                  nv' = List.union g [z]
                              in
                                (nv', g, z, r)
    infer' (v, (Sem.And e1 e2)) = let (v1, g1, t1, r1) = infer' (v, e1)
                              (v2, g2, t2, r2) = infer' (v, e2)
                              s = [(s1,s2)|(x,s1) <- g1, (y,s2) <- g2, x==y]
                              z = fresh s
                              nv' = List.union s [z]
                          in
                            (nv', List.union g1 g2, z, List.union (r1
                                (List.union r2 s))
    infer' (v, (Sem.Or e1 e2)) = let (v1, g1, t1, r1) = infer' (v, e1)
                              (v2, g2, t2, r2) = infer' (v, e2)
                              s = [(s1,s2)|(x,s1) <- g1, (y,s2) <- g2, x==y]
                              z = fresh s
                              nv' = List.union s [z]
                          in
                            (nv', List.union g1 g2, z, List.union (r1
                                (List.union r2 s))
    infer' (v, (Sem.Lt e1 e2)) = let (v1, g1, t1, r1) = infer' (v, e1)
                              (v2, g2, t2, r2) = infer' (v, e2)
                              s = [(s1,s2)|(x,s1) <- g1, (y,s2) <- g2, x==y]
                              z = fresh s
                              nv' = List.union s [z]
                          in
                            (nv', List.union g1 g2, z, List.union (r1
                                (List.union r2 s))
    infer' (v, (Sem.Gt e1 e2)) = let (v1, g1, t1, r1) = infer' (v, e1)
                              (v2, g2, t2, r2) = infer' (v, e2)
                              s = [(s1,s2)|(x,s1) <- g1, (y,s2) <- g2, x==y]
                              z = fresh s
                              nv' = List.union s [z]
                          in
                            (nv', List.union g1 g2, z, List.union (r1
                                (List.union r2 s))
    infer' (v, (Sem.Eq e1 e2)) = let (v1, g1, t1, r1) = infer' (v, e1)
                          (v2, g2, t2, r2) = infer' (v, e2)
                          s = [(s1,s2)|(x,s1) <- g1, (y,s2) <- g2, x==y]
                          z = fresh s
                          nv' = List.union s [z]
                      in
                        (nv', List.union g1 g2, z, List.union (r1
                            (List.union r2 s))
    infer' (v, (Sem.If c e1 e2)) = let (v1, g1, t1, r1) = infer' (v, e1)
                          (v2, g2, t2, r2) = infer' (v, e2)
                          s = [(s1,s2)|(x,s1) <- g1, (y,s2) <- g2, x==y]
                          z = fresh s
                          nv' = List.union s [z]
                      in
                        (nv', List.union g1 g2, z, List.union (r1
                            (List.union r2 s))
    -- Por completar
    infer' (v, (Sem.Let id e1 e2)) = let
                          (v1, g1, t1, r1) = infer' (v, e1)
                          (v2, g2, t2, r2) = infer' (v, e2)
                          s = [(s1,s2)|(x,s1) <- g1, (y,s2) <- g2, x==y]
                          z = fresh s
                          nv' = List.union s [z]
                      in
                          (nv', List.union g1 g2, z, List.union (r1
                            (List.union r2 s))
    infer' (nv, (Sem.Fn x e)) = let (nv', g, t, r) = infer' (nv e)
                                in case find x g of
                                    Just t' -> (nv', g \\ [(x,t')],t' :-> t, r)
                                    Nothing -> let t' = fresh nv'
                                                    nv'' = List.union nv' [t']
                                                in (nv'', g, t' :-> t, r)
    infer' (nv, (Sem.App e1 e2)) = let (nv1, g1, t1, r1) = infer' (nv, e1)
                                      (nv2, g2, t2, r2) = infer' (nv1, e2)
                                      s = [(s1,s2)|(x,s1) <- g1, (y,s2) <- g2, x==y]
                                      z = fresh nv2
                                      nv' = LIst.union nv2 [z]
                                  in
                                    (nv', List.union g1 g2, z, r1 'List.Union' r2 'List.Union' s 'List.Union' [(t1, t2 :-> z)])

    infer :: Expr -> (Ctxt, Type)
    infer e = let (v, g, t, r) = infer' ([], e)
                    umg = (Unifier.µ r)
              in (substCtxt g umg, subst t umg)


-- Maybe puede ser nothing o el tipo que le estoy pasando
-- infer' (v, (Sem.Fix x e)) = let (v', g, t, c) = infer' (v,e)
-- in case (find x g) of
--     just t' ->  let g' = ((filter (\d -> x /=(fst d)) g)
--     c' = List.union [(t, t)]
--     in (v', g', t, c')
--     Nothing -> let z = frexh v'
--     v'' = List.union v' [z]
--     in (v'', g, z, c)
--     (v', _, t,_)
