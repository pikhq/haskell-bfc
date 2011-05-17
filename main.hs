import Control.DeepSeq
import Control.Monad.State

data BF = Add Int Int
        | Move Int
        | In
        | Out
        | Loop Int [BF]
        | Set Int Int
          deriving (Show, Eq)

data Syscalls = Read
              | Write
              | Indeterm
                deriving Eq

instance NFData BF where
    rnf (Add a b) = a `seq` b `seq` ()
    rnf (Move a) = a `seq` ()
    rnf (Loop a b) = a `seq` b `deepseq` ()
    rnf (Set a b) = a `seq` b `seq` ()
    rnf x = x `seq` ()

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
opt = omitInit . fixPointOfOpts
    where omitInit (Loop _ _ : xs) = omitInit xs
          omitInit (Set _ 0 : xs) = omitInit xs
          omitInit x = x

-- Finds the fixed point of the optimisation functions; runs the optimisations
-- until nothing changes.
-- This is strict because laziness involves somewhat excessive memory usage.
fixPointOfOpts :: [BF] -> [BF]
fixPointOfOpts x = if allPasses x == x then x else fixPointOfOpts $!! allPasses x
    where f $!! x = x `deepseq` f x

allPasses = intoLoops . offset . dce . sets . rle

intoLoops (Loop a x : xs) = Loop a (allPasses x) : intoLoops xs
intoLoops (x : xs) = x : intoLoops xs
intoLoops [] = []

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
dce (Add a x : Set b y : xs)
    | a == b = dce $ Set b y : xs
    | otherwise = Add a x : (dce $ Set b y : xs)
dce (Set a x : Set b y : xs)
    | a == b = dce $ Set b y : xs
    | otherwise = Set a x : (dce $ Set b y : xs)
dce (Add _ 0 : xs) = dce xs
dce (Move 0 : xs) = dce xs
dce (x : xs) = x : dce xs
dce [] = []

-- Attempt to reduce the amount of pointer movements done
offset :: [BF] -> [BF]
offset (Move x : Add a y : xs) = Add (a+x) y : (offset $ Move x : xs)
offset (Move x : Set a y : xs) = Set (a+x) y : (offset $ Move x : xs)
offset (Move x : Loop a y : xs) = Loop (a+x) (Move x : y ++ [Move (x*(-1))]) : (offset $ Move x : xs)
offset (x : xs) = x : offset xs
offset [] = []

----
-- Compilation
----
comp :: [BF] -> String
comp xs = prelude ++ codeGen xs ++ postlude

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

codeGen :: [BF] -> String
codeGen xs = evalState (codeGen' xs) (0, Indeterm)
    where codeGen' :: [BF] -> State (Int, Syscalls) String
          codeGen' (In:xs) = do (label, sys) <- get
                                put (label+1, Read)
                                next <- codeGen' xs
                                let setebx = case sys of Read -> ""
                                                         Write -> "\tdec bl\n"
                                                         Indeterm -> "\txor ebx,ebx\n"
                                return $ "\tmov eax, esp\n" ++
                                         setebx ++
                                         "\tint 80h\n" ++
                                         "\tcmp eax, 1\n" ++
                                         "\tje L" ++ (show label) ++ "\n" ++
                                         "\tmov byte [ecx], 0\n" ++
                                         "L" ++ (show label) ++ ":\n" ++ next
          codeGen' (Out:xs) = do sys <- getSyscall
                                 putSyscall Write
                                 next <- codeGen' xs
                                 let setebx = case sys of Read -> "\tinc bl\n"
                                                          Write -> ""
                                                          Indeterm -> "\tmov ebx,edx\n"
                                 return $ "\tmov eax, ebp\n" ++
                                          setebx ++
                                          "\tint 80h\n" ++ next
          codeGen' (Add a x:xs) = do next <- codeGen' xs
                                     let offby = if a == 0 then "" else " + " ++ (show a)
                                     return $ (case x of 1  -> "\tinc byte [ecx" ++ offby ++ "]"
                                                         -1 -> "\tdec byte [ecx" ++ offby ++ "]"
                                                         _  -> "\tadd byte [ecx" ++ offby ++ "], " ++ (show x)) ++ "\n" ++ next
          codeGen' (Move x:xs) = do next <- codeGen' xs
                                    return $ (case x of 1  -> "\tinc ecx"
                                                        -1 -> "\tdec ecx"
                                                        _  -> "\tadd ecx, " ++ (show x)) ++ "\n" ++ next
          codeGen' (Loop a x:xs) = do label <- getLabel
                                      put (label+2, Indeterm)
                                      loopContents <- codeGen' x
                                      putSyscall Indeterm
                                      next <- codeGen' xs
                                      let offby = if a == 0 then "" else " + " ++ (show a)
                                          bLabel = "L" ++ show label
                                          eLabel = "L" ++ show (label+1)
                                      return $ "\tcmp byte [ecx" ++ offby ++ "], 0\n" ++
                                               "\tje " ++ bLabel ++ "\n" ++
                                               eLabel ++ ":\n" ++
                                               loopContents ++
                                               "\tcmp byte [ecx" ++ offby ++ "], 0\n" ++
                                               "\tjne " ++ eLabel ++ "\n" ++
                                               bLabel ++ ":\n" ++ next
          codeGen' (Set a x:xs) = do next <- codeGen' xs
                                     let offby = if a == 0 then "" else " + " ++ (show a)
                                     return $ "\tmov byte [ecx" ++ offby ++ "], " ++ (show x) ++ "\n" ++ next
          codeGen' [] = return []

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
main = getContents >>= putStrLn . comp . opt . parse
