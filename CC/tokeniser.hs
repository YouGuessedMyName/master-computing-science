import Data.Char

data Token
    =
    -- Interpunction
    CommaToken | SemiColumnToken
    -- Field
    | DotToken | HdToken | TlToken
    -- Statements
    | IsToken | IfToken | ElseToken | WhileToken | ReturnToken
    -- Basic types
    | VoidToken | IntToken | BoolToken | CharToken
    -- True and False
    -- Operators
    | PlusToken | MinusToken | TimesToken | DivideToken | ModToken
    | EqualToken | LessToken | GreaterToken | LeqToken | GeqToken | NeqToken
    | AndToken | OrToken
    | ColumnToken | NotToken
    -- Braces
    | BraceOpen | BraceClose 
    | SquareBraceOpen | SquareBraceClose
    | CurlyBraceOpen | CurlyBraceClose
    -- Misc
    | IntLit Integer | BoolLit Bool
    | IdentToken String
    | ErrToken String
  deriving (Show, Eq)

tokenise :: [Char] -> [Token]
-- Interpunction
tokenise (',':xs) = CommaToken:tokenise xs
tokenise (';':xs) = SemiColumnToken:tokenise xs
-- Field
tokenise ('.':xs) = DotToken:tokenise xs
tokenise ('h':'d':xs) = HdToken:tokenise xs
tokenise ('t':'l':xs) = TlToken:tokenise xs
-- Operators
tokenise ('+':xs) = PlusToken:tokenise xs
tokenise ('-':xs) = MinusToken:tokenise xs
tokenise ('*':xs) = TimesToken:tokenise xs
tokenise ('/':xs) = DivideToken:tokenise xs
tokenise ('%':xs) = ModToken:tokenise xs  
tokenise ('=':'=':xs) = PlusToken:tokenise xs
tokenise ('<':'=':xs) = LeqToken:tokenise xs
tokenise ('>':'=':xs) = GeqToken:tokenise xs
tokenise ('>':xs) = GreaterToken:tokenise xs
tokenise ('<':xs) = LessToken:tokenise xs
tokenise ('!':'=':xs) = NeqToken:tokenise xs
tokenise ('&':'&':xs) = AndToken:tokenise xs
tokenise ('|':'|':xs) = OrToken:tokenise xs
tokenise (':':xs) = ColumnToken:tokenise xs
tokenise ('!':xs) = NotToken:tokenise xs
-- Statements
tokenise ('=':xs) = IsToken:tokenise xs
tokenise ('i':'f':xs) = IfToken:tokenise xs
tokenise ('e':'l':'s':'e':xs) = ElseToken:tokenise xs
tokenise ('w':'h':'i':'l':'e':xs) = WhileToken:tokenise xs
tokenise ('r':'e':'t':'u':'r':'n':xs) = ReturnToken:tokenise xs
-- Basic Types
tokenise ('V':'o':'i':'d':xs) = VoidToken:tokenise xs
tokenise ('I':'n':'t':xs) = IntToken:tokenise xs
tokenise ('B':'o':'o':'l':xs) = BoolToken:tokenise xs
tokenise ('C':'h':'a':'r':xs) = BoolToken:tokenise xs
-- Braces
tokenise ('(':xs) = BraceOpen:tokenise xs
tokenise (')':xs) = BraceClose:tokenise xs
tokenise ('{':xs) = CurlyBraceOpen:tokenise xs
tokenise ('}':xs) = CurlyBraceClose:tokenise xs
tokenise ('[':xs) = SquareBraceOpen:tokenise xs
tokenise (']':xs) = SquareBraceClose:tokenise xs
-- Misc
tokenise ('T':'r':'u':'e':xs) = BoolLit True : tokenise xs
tokenise ('F':'a':'l':'s':'e':xs) = BoolLit False : tokenise xs
tokenise (c:xs)
    | isSpace c = tokenise xs
    | isDigit c = spanToken isDigit (IntLit . read) (c:xs)
    | isAlpha c = spanToken isAlphaNum IdentToken (c:xs)
    | otherwise = ErrToken ("Unrecognised character: " ++ show c) : tokenise xs
tokenise [] = []

-- span splitst de lijst gebaseerd op de predicate: eerste return is t/m waar predicate true, rest is false.
-- pred:
-- tfun: Functie die dit specifiek parsed
-- rest van de lijst, wordt geparsed zodra we hier klaar zijn.
spanToken :: (Char -> Bool) -> ([Char] -> Token) -> [Char] -> [Token]
spanToken pred tfun cs = tfun tchars:tokenise rest
  where (tchars, rest) = span pred cs

main = do  
        contents <- readFile "tests/2D.spl"
        print contents
        print "\nTokenized:\n"
        print (tokenise contents)

-- main = putStrLn (show $ tokenise "1*/*blurp*/(x+50)")