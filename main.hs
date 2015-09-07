import Debug.SimpleReflect

data Val = Zero | NonZero deriving (Show)
data RelKind = Eq | Diff deriving (Show)
type MovFunc = (Expr, Expr, Expr, Expr) -> (Expr, Expr, Expr, Expr)
type Rel = (RelKind, (Int, Int))
type Rels = [Rel]
type Vals = [Val]

shiftRel :: Rel -> Int -> Rel
shiftRel (kind, (a, b)) offset = (kind, ((shift a), (shift b)))
  where shift x
            | x >= offset = x + 1
            | otherwise   = x

shiftVals :: Vals -> Int -> Vals
shiftVals vals offset = (take offset vals) ++ [Zero] ++ (drop offset vals)

type MergeLogic = (Vals, Rels, MovFunc)

relKindSeqs :: [[RelKind]]
relKindSeqs = [] : [p : x | x <- relKindSeqs, p <- [Diff, Eq]]

relSeqs :: [Rels]
relSeqs = map addRange relKindSeqs
  where addRange x = zipWith putRange x [0 .. length x - 1]
        putRange x n = (x, (n, n + 1))

initRels = takeWhile ((>=) 3 . length) relSeqs

movFuncFromAdjRels :: Rels -> MovFunc
movFuncFromAdjRels rels = merge rels id
  where merge [] _ = id
        merge ((Diff, _):[]) f = merge [] f . id
        merge ((Eq, (a, _)):[]) f = merge [] f . mergeAt a
        merge ((Diff, _):y:ys) f = merge (y:ys) f . id
        merge ((Eq, (a, _)):(_, rng):ys) f = merge (map shiftRng ((Diff, rng):ys)) f . mergeAt a
        shiftRng (k, (a, b)) = (k, (a - 1, b - 1))

mergeAt :: Int -> MovFunc
mergeAt p = \ (a, b, c, d) -> case p of
  0 -> (a + 1, c, d, 0)
  1 -> (a, b + 1, d, 0)
  2 -> (a, b, c + 1, 0)

valsFromInitRels :: Rels -> Vals
valsFromInitRels rels = take (length rels + 1) $ repeat NonZero
