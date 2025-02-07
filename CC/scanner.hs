import Data.Char

data Token
    = MinusToken | PlusToken | TimesToken | DivideToken
    | BraceOpen | BraceClose
    | NumToken Integer | IdentToken String
    | ErrToken String
  deriving (Show, Eq)

tokenise :: [Char] -> [Token]
tokenise ('/':'*':xs) = gulp xs
    where
        gulp ('*':'/':rest) = tokenise rest
        gulp (c:rest) = gulp rest
        gulp [] = []
tokenise ('/':'/':xs) = tokenise $ dropWhile (/='\n') xs
tokenise ('(':xs) = BraceOpen:tokenise xs
tokenise (')':xs) = BraceClose:tokenise xs
tokenise ('/':xs) = DivideToken:tokenise xs
tokenise ('*':xs) = TimesToken:tokenise xs
tokenise ('+':xs) = PlusToken:tokenise xs
tokenise ('-':xs) = MinusToken:tokenise xs
tokenise (c:xs)
    | isSpace c = tokenise xs
    | isDigit c = spanToken isDigit (NumToken . read) (c:xs)
    | isAlpha c = spanToken isAlphaNum IdentToken (c:xs)
    | otherwise = ErrToken ("Unrecognised character: " ++ show c) : tokenise xs
tokenise [] = []

spanToken :: (Char -> Bool) -> ([Char] -> Token) -> [Char] -> [Token]
spanToken pred tfun cs = tfun tchars:tokenise rest
  where (tchars, rest) = span pred cs

main = putStrLn (show $ tokenise "1*/*blurp*/(x+50)")
