import data.buffer
import .core

namespace parser.char

open parser

@[reducible] def t := parser char

-- def parser = parser
/-- Matches a string.  Does not consume input in case of failure. -/
def str (s : string) : parser char unit :=
decorate_error s $ s.to_list.mmap' el

def many_char (p : parser char char) : parser char string :=
list.as_string <$> many p

-- universe u

/-- Runs a parser on the given input.  The parser needs to match the complete input. -/
def run_string {α : Type} (p : parser char α) (input : string) : sum string α :=
run p input.to_char_buffer

end parser.char
