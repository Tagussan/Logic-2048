import Debug.SimpleReflect
import Data.List
import Data.List.Split
import Data.String
import Text.Regex
import Text.Regex.Posix

data Val = Zero | NonZero deriving (Eq, Show)
data RelKind = Eq | Diff deriving (Eq, Show)
type MovFunc = (Expr, Expr, Expr, Expr) -> (Expr, Expr, Expr, Expr)
type Rel = (RelKind, (Int, Int))
type Rels = [Rel]
type Vals = [Val]
type PaddedValsSet = [Vals]
type PaddedVals = Vals
type InitCond = (Rels, Vals)
type Logic = (InitCond, MovFunc)

shiftRel :: Int -> Rel -> Rel
shiftRel offset (kind, (a, b)) = (kind, ((shift a), (shift b)))
  where shift x
          | x >= offset = x + 1
          | otherwise   = x

shiftVals :: Int -> Vals -> Vals
shiftVals offset vals = (take offset vals) ++ [Zero] ++ (drop offset vals)

relKindSeqs :: [[RelKind]]
relKindSeqs = [] : [p : x | x <- relKindSeqs, p <- [Diff, Eq]]

relSeqs :: [Rels]
relSeqs = map addRange relKindSeqs
  where addRange x = zipWith putRange [0 .. length x - 1] x
        putRange n x = (x, (n, n + 1))

initRels = takeWhile ((>=) 3 . length) relSeqs

initFuncFromVals :: Vals -> MovFunc
initFuncFromVals vals = foldr assignZero id $ zip [0 .. length vals - 1] vals
  where assignZero (ind, val) func
          | val == Zero = (assignFunc ind) . func
          | otherwise = func
        assignFunc ind = \ (a, b, c, d) -> case ind of
          0 -> (0, b, c, d)
          1 -> (a, 0, c, d)
          2 -> (a, b, 0, d)
          3 -> (a, b, c, 0)

movFuncFromAdjRels :: Rels -> MovFunc
movFuncFromAdjRels rels = merge rels id
  where merge [] _ = id
        merge ((Diff, _):[]) f = merge [] f . id
        merge ((Eq, (a, _)):[]) f = merge [] f . mergeFuncAt a
        merge ((Diff, _):y:ys) f = merge (y:ys) f . id
        merge ((Eq, (a, _)):(_, rng):ys) f = merge (map shiftRng ((Diff, rng):ys)) f . mergeFuncAt a
        shiftRng (k, (a, b)) = (k, (a - 1, b - 1))

mergeFuncAt :: Int -> MovFunc
mergeFuncAt p = \ (a, b, c, d) -> case p of
  0 -> (a + 1, c, d, 0)
  1 -> (a, b + 1, d, 0)
  2 -> (a, b, c + 1, 0)

shiftFuncAt :: Int -> MovFunc
shiftFuncAt p = \ (a, b, c, d) -> case p of
  0 -> (b, c, d, 0)
  1 -> (a, c, d, 0)
  2 -> (a, b, d, 0)
  3 -> (a, b, c, d)


valsFromInitRels :: Rels -> Vals
valsFromInitRels rels = take (length rels + 1) $ repeat NonZero

initVals = map valsFromInitRels initRels

initLogics = (([],[]), id) : map mkLogic initRels
  where mkLogic rels = ((rels, vals), movFunc)
          where vals = valsFromInitRels rels
                movFunc = (movFuncFromAdjRels rels)

debugMovFunc :: MovFunc -> (Expr, Expr, Expr, Expr)
debugMovFunc func = func (x, y, z, w)

debugLogic :: Logic -> (InitCond, (Expr, Expr, Expr, Expr))
debugLogic (initCond, func) = (initCond, func (x, y, z, w))

insertAt :: Int -> a -> [a] -> [a]
insertAt pos elm trg = (take pos trg) ++ [elm] ++ (drop pos trg)

paddedAll :: (Eq a) => a -> [a] -> [[a]]
paddedAll elm trg = trg : nub [padded n ary | ary <- paddedAll elm trg, n <- [0 .. length trg]]
  where padded n ary = insertAt n elm ary

pickSeq :: (a -> Bool) -> [a] -> [a]
pickSeq f = takeWhile f . dropWhile (not . f)

paddedValsSet :: Vals -> PaddedValsSet
paddedValsSet vals = pickSeq (\ x -> ((==) 4 (length x))) $ paddedAll Zero vals

shiftRelsByPaddedVals :: PaddedVals -> Rels -> Rels
shiftRelsByPaddedVals vals rels = foldr shift rels (reverse valsWithInd)
  where valsWithInd = zip vals [0 .. length vals - 1]
        shift (val, ind) rels_ = if val == Zero then map (shiftRel ind) rels_ else rels_

shiftFuncByPaddedVals :: PaddedVals -> MovFunc -> MovFunc
shiftFuncByPaddedVals vals func = func . (foldr shift id valsWithInd)
  where valsWithInd = zip vals [0 .. length vals - 1]
        shift (val, ind) func_ = if val == Zero then (shiftFuncAt ind) . func_ else func_

padLogic :: Logic -> [Logic]
padLogic ((rels, vals), func) = map mkLogic $ paddedValsSet vals
  where mkLogic paddedVals = ((shiftRelsByPaddedVals paddedVals rels, paddedVals), (shiftFuncByPaddedVals paddedVals func) . (initFuncFromVals paddedVals))

paddedLogics = concat $ map padLogic initLogics

strLogic = show . debugLogic

prettyShowRels :: Rels -> String
prettyShowRels rels = intercalate " && " $ map prettyRel rels
  where prettyRel (kind, (a, b)) = "x" ++ (show a) ++ " " ++ op ++ " x" ++ (show b)
          where op = case kind of
                       Diff -> "!="
                       Eq -> "=="

prettyShowVals :: Vals -> String
prettyShowVals vals = intercalate " && " $ map prettyVal $ zip [0 .. length vals - 1] vals
  where prettyVal (ind, kind) = "x" ++ (show ind) ++ " " ++ op ++ " 0"
          where op = case kind of
                       Zero -> "=="
                       NonZero -> "!="

prettyShowMovFunc :: MovFunc -> String
prettyShowMovFunc func = (intercalate ";" assignStrs) ++ ";"
  where assignStrs = zipWith assignStr [0 .. length varStrs - 1] varStrs
        assignStr ind varStr = "y" ++ (show ind) ++ " <= " ++ varStr
        varStrs = map replaceVar ((\ (a1, a2, a3, a4) -> map show [a1, a2, a3, a4]) (func (a, b, c, d)))
        replaceVar str = foldr (\ (from, to) origStr -> replace from to origStr) str mappings
        mappings = zip ["a", "b", "c", "d"] ["x0", "x1", "x2", "x3"]
        replace old new = intercalate new . splitOn old

prettyPrintLogic ((rels, vals), func) = mapM_ putStr [conds, ",", prettyShowMovFunc func, "\n"]
  where conds
          | prettyShowRels rels /= "" = prettyShowVals vals ++ " && " ++ prettyShowRels rels
          | otherwise = prettyShowVals vals

prettyPrintAllLogic = mapM_ prettyPrintLogic paddedLogics

type LogicWithValidity = (Logic, Bool)
logicWithValidity :: Logic -> LogicWithValidity
logicWithValidity logic@((rels, vals), func)
                     | valid vals func = (logic, True)
                     | otherwise = (logic, False)
                     where valid vals func = not $ all sameKind $ zip vals funcList
                             where funcList = (\ (a1, a2, a3, a4) -> map show [a1, a2, a3 ,a4]) (func (x, y, z, w))
                                   sameKind (val, var)
                                     | val == Zero = if var == "0" then True else False
                                     | val == NonZero = if var /= "0" then True else False

prettyPrintLogicWithValidity (((rels, vals), func), validity) = mapM_ putStr [conds, ",", prettyShowMovFunc func, prettyShowValidity validity, "\n"]
  where conds
          | prettyShowRels rels /= "" = prettyShowVals vals ++ " && " ++ prettyShowRels rels
          | otherwise = prettyShowVals vals
        prettyShowValidity validity = if validity then "movable <= 1;" else "movable <= 0;"

prettyPrintAllLogicWithValidity = mapM_ prettyPrintLogicWithValidity $ map logicWithValidity paddedLogics
-- main = prettyPrintAllLogicWithValidity

relsToBits rels = foldr relToBit "xxxxxx" rels
  where relToBit (k, rng) str = replaceBitAt (rngToPos rng)
          where replaceBitAt i = replaceN str i (kindBit k)
        rngToPos rng = case rng of
                         (0, 1) -> 0
                         (1, 2) -> 1
                         (2, 3) -> 2
                         (0, 2) -> 3
                         (1, 3) -> 4
                         (0, 3) -> 5
        kindBit Eq = "0"
        kindBit Diff = "1"
        replaceN xs n new = take n xs ++ new ++ drop (n + 1) xs

showBinLen2 i = case i of
                  0 -> "00"
                  1 -> "01"
                  2 -> "10"
                  3 -> "11"

movFuncToBits func = concat $ map packToBit varStrs
  where varStrs = map replaceVar ((\ (a1, a2, a3, a4) -> map show [a1, a2, a3, a4]) (func (a, b, c, d)))
        replaceVar str = foldr (\ (from, to) origStr -> replace from to origStr) str mappings
        mappings = zip ["a", "b", "c", "d"] ["x0", "x1", "x2", "x3"]
        replace old new = intercalate new . splitOn old
        packToBit varStr = varFrom ++ isAdd ++ isZero
          where parts = ((varStr =~ "^(x?)([0-9])(.+.1)?$" :: [[String]]) !! 0)
                varFrom = (showBinLen2 . read) (parts !! 2)
                isAdd = if (parts !! 3) == "" then "0" else "1"
                isZero = if (parts !! 1) == "x" then "0" else "1"

genPossibleBits bits = if elem 'x' bits
                          then let left = takeWhile ((/=) 'x') bits
                                   right = tail $ dropWhile ((/=) 'x') bits
                                in
                                  concatMap genPossibleBits [left ++ [p] ++ right | p <- "01"]
                          else [bits]

