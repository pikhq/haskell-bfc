import Control.Monad.State

data BF = Add !Int !Int
        | Move !Int
        | In
        | Out
        | Loop !Int [BF]
        | Set !Int !Int
          deriving (Show, Eq)

data Syscalls = Read
              | Write
              | Indeterm
                deriving Eq

----
-- Parser
----
parse :: String -> [BF]
parse =
    let parse' :: String -> ([BF], String)
        parse' (x:xs) =
            case x of
              '+' -> (Add 0 1 : next, rem)
              '-' -> (Add 0 (-1) : next, rem)
              '>' -> (Move 1 : next, rem)
              '<' -> (Move (-1) : next, rem)
              ',' -> (In : next, rem)
              '.' -> (Out : next, rem)
              '[' -> (Loop 0 next : parsedRem, unParsedRem)
                  where (parsedRem, unParsedRem) = parse' rem
              ']' -> ([], xs)
              _   -> (next, rem)
            where (next, rem) = parse' xs
        parse' [] = ([], [])
    in fst . parse'

----
-- Optimisation
----
opt :: [BF] -> [BF]
opt = dropWhile f . allPasses . offset 0 0
    where f (Loop _ _) = True
          f (Set _ 0) = True
          f _ = False

allPasses :: [BF] -> [BF]
allPasses = intoLoops . dce . sets . rle

intoLoops :: [BF] -> [BF]
intoLoops = map f
            where f (Loop a x) = Loop a (allPasses x)
                  f x = x

-- Run-length encode addition and movement operations
rle :: [BF] -> [BF]
rle (Add a x : Add b y : xs)
    | a == b = rle $ Add a (x + y) : xs
    | otherwise = Add a x : (rle $ Add b y : xs)
rle (Move x : Move y : xs) = rle $ Move (x + y) : xs
rle (x : xs) = x : rle xs
rle [] = []

-- Attempt to pattern match against all common "setting" idioms
-- and convert into the Set instruction
sets :: [BF] -> [BF]
sets (Loop a [Add b x] : xs) 
    | a == b && (x == (-1) || x == 1)  = sets $ Set a 0 : xs
    | otherwise = Loop a [Add b x] : sets xs
sets (Set a x : Add b y : xs)
    | a == b = sets $ Set a (x+y) : xs
    | otherwise = Set a x : (sets $ Add b y : xs)
sets (x : xs) = x : sets xs
sets [] = []

-- This is, currently, a fairly mundane dead-code optimisation pass.
-- Should be much improved when I get around to doing constant folding.
dce :: [BF] -> [BF]
dce (Loop a x : Loop b y : xs) 
    | a == b = dce $ Loop a x : xs
    | otherwise = Loop a x : (dce $ Loop b y : xs)
dce (Loop a x : Set b y : xs)
    | a == b && y == 0 = dce $ Loop a x : xs
    | otherwise = Loop a x : (dce $ Set b y : xs)
dce (Set a x : Loop b y : xs)
    | a == b && x == 0 = dce $ Set a x : xs
    | otherwise = Set a x : (dce $ Loop b y : xs)
dce (Set a x : Set b y : xs)
    | a == b = dce $ Set b y : xs
    | otherwise = Set a x : (dce $ Set b y : xs)
dce (Add a x : Set b y : xs)
    | a == b = dce $ Set b y : xs
    | otherwise = Add a x : (dce $ Set b y : xs)
dce (Add _ 0 : xs) = xs
dce (Move 0 : xs) = xs
dce (x : xs) = x : dce xs
dce [] = []

-- Attempt to reduce the amount of pointer movements done
offset :: Int -> Int -> [BF] -> [BF]
offset m n (Loop a y : xs) = Loop (a+m) (offset m (-m) y) : offset m n xs
offset m n (Move x : xs) = offset (m+x) n xs
offset m n (Add a x : xs) = Add (a+m) x : offset m n xs
offset m n (Set a x : xs) = Set (a+m) x : offset m n xs
offset 0 n (x : xs) = x : offset 0 n xs
offset m n (x : xs) = Move m : x : offset 0 n xs
offset m n []
  | m /= (-n) = [Move (m+n)]
  | otherwise = []

----
-- Compilation
----
comp :: [BF] -> IO ()
comp x = do
  putStr prelude
  sequence_ . codeGen $ x
  putStr postlude

prelude = "BITS 32\n" ++ 
          "SECTION .text\n" ++
          "global _start\n" ++
          "_start:\n" ++
          "\tmov dl, 1\n" ++ 
          "\tmov esp, 3\n" ++
          "\tmov ebp, 4\n" ++
          "\tmov ecx, data\n"

postlude = "\tmov eax, 1\n" ++
           "\tmov ebx, 0\n" ++
           "\tint 80h\n" ++
           "\n" ++
           "SECTION .bss\n" ++
           "data\tresb 30000\n"

codeGen :: [BF] -> [IO ()]
codeGen xs = evalState (mapM codeGen' xs) (0, Indeterm)
    where codeGen' :: BF -> State (Int, Syscalls) (IO ())
          codeGen' In = do (label, sys) <- get
                           put (label+1, Read)
                           let setebx = case sys of Read -> ""
                                                    Write -> "\tdec bl\n"
                                                    Indeterm -> "\txor ebx,ebx\n"
                           return $ do putStrLn "\tmov eax, esp"
                                       putStr setebx
                                       putStr $ "\tint 80h\n" ++
                                                "\tcmp eax, 1\n" ++
                                                "\tje L" ++ (show label) ++ "\n" ++
                                                "\tmov byte [ecx], 0\n" ++
                                                "L" ++ (show label) ++ ":\n"
          codeGen' Out = do sys <- getSyscall
                            putSyscall Write
                            let setebx = case sys of Read -> "\tinc bl\n"
                                                     Write -> ""
                                                     Indeterm -> "\tmov ebx,edx\n"
                            return . putStrLn $ "\tmov eax, ebp\n" ++
                                                setebx ++
                                                "\tint 80h"
          codeGen' (Add a x) = return . putStrLn $ case x of 1  -> "\tinc byte [ecx" ++ offby ++ "]"
                                                             -1 -> "\tdec byte [ecx" ++ offby ++ "]"
                                                             _  -> "\tadd byte [ecx" ++ offby ++ "], " ++ (show x)
            where offby = if a == 0 then "" else " + " ++ (show a)
          codeGen' (Move x) = return . putStrLn $ case x of 1  -> "\tinc ecx"
                                                            -1 -> "\tdec ecx"
                                                            _  -> "\tadd ecx, " ++ (show x)
          codeGen' (Loop a x) = do label <- getLabel
                                   put (label+2, Indeterm)
                                   loopContents <- mapM codeGen' x
                                   putSyscall Indeterm
                                   let offby = if a == 0 then "" else " + " ++ (show a)
                                       bLabel = "L" ++ show label
                                       eLabel = "L" ++ show (label+1)
                                   return $ do putStrLn $ "\tcmp byte [ecx" ++ offby ++ "], 0\n" ++
                                                                  "\tje " ++ bLabel ++ "\n" ++
                                                                  eLabel ++ ":"
                                               sequence_ loopContents
                                               putStrLn $ "\tcmp byte [ecx" ++ offby ++ "], 0\n" ++
                                                          "\tjne " ++ eLabel ++ "\n" ++
                                                          bLabel ++ ":"
          codeGen' (Set a x) = return . putStrLn $ "\tmov byte [ecx" ++ offby ++ "], " ++ (show x)
              where offby = if a == 0 then "" else " + " ++ (show a)

-- Some minor utility functions for the above codeGen' function
getLabel :: State (Int, a) Int
getLabel = gets $ \(label, _) -> label

putLabel :: Int -> State (Int, a) ()
putLabel x = modify $ \(label, syscall) -> (x, syscall)

getSyscall :: State (a, Syscalls) Syscalls
getSyscall = gets $ \(_, syscall) -> syscall

putSyscall :: Syscalls -> State (a, Syscalls) ()
putSyscall x = modify $ \(label, syscall) -> (label, x)

----
-- The inevitable interaction with the real world
----

main :: IO ()
main = getContents >>= comp . opt . parse
