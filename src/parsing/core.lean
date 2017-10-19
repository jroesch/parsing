import data.buffer data.dlist

instance (α : Type) [has_to_string α] : has_to_string (buffer α) :=
⟨ fun b, to_string $ b.to_list ⟩

universes u v

inductive parse_result (α : Type u)
| done (pos : ℕ) (result : α) : parse_result
| fail (pos : ℕ) (expected : dlist string) : parse_result

def parser (elem : Type v) (α : Type u) :=
∀ (input : buffer elem) (start : ℕ), parse_result α

-- todo: refactor into parser core
namespace parser

-- Type polymorphism is restricted here because of monad.bind
variables {elem α β γ : Type}

protected def bind (p : parser elem α) (f : α → parser elem β) : parser elem β :=
λ input pos, match p input pos with
| parse_result.done pos a           := f a input pos
| parse_result.fail ._ pos expected := parse_result.fail β pos expected
end

protected def pure (a : α) : parser elem α :=
λ input pos, parse_result.done pos a

private lemma id_map (p : parser elem α) : parser.bind p parser.pure = p :=
begin
apply funext, intro input,
apply funext, intro pos,
dunfold parser.bind,
cases (p input pos); exact rfl
end

private lemma bind_assoc (p : parser elem α) (q : α → parser elem β) (r : β → parser elem γ) :
  parser.bind (parser.bind p q) r = parser.bind p (λ a, parser.bind (q a) r) :=
begin
apply funext, intro input,
apply funext, intro pos,
dunfold parser.bind,
cases (p input pos); try {dunfold bind},
cases (q result input pos_1); try {dunfold bind},
all_goals {refl}
end

protected def fail (msg : string) : parser elem α :=
λ _ pos, parse_result.fail α pos (dlist.singleton msg)

instance : monad_fail (parser elem) :=
{ pure := @parser.pure elem,
  bind := @parser.bind elem,
  fail := @parser.fail elem,
  id_map := @id_map elem,
  pure_bind := λ _ _ _ _, rfl,
  bind_assoc := @bind_assoc elem }

protected def failure : parser elem α :=
λ _ pos, parse_result.fail α pos dlist.empty

protected def orelse (p q : parser elem α) : parser elem α :=
λ input pos, match p input pos with
| parse_result.fail ._ pos₁ expected₁ :=
  if pos₁ ≠ pos then parse_result.fail _ pos₁ expected₁ else
  match q input pos with
  | parse_result.fail ._ pos₂ expected₂ :=
    if pos₁ < pos₂ then
      parse_result.fail _ pos₁ expected₁
    else if pos₂ < pos₁ then
      parse_result.fail _ pos₂ expected₂
    else -- pos₁ = pos₂
      parse_result.fail _ pos₁ (expected₁ ++ expected₂)
  | ok := ok
  end
  | ok := ok
end

instance : alternative (parser elem) :=
{ parser.monad_fail with
  failure := @parser.failure elem,
  orelse := @parser.orelse elem }

instance : inhabited (parser elem α) :=
⟨parser.failure⟩

/-- Overrides the expected token name, and does not consume input on failure. -/
def decorate_errors (msgs : thunk (list string)) (p : parser elem α) : parser elem α :=
λ input pos, match p input pos with
| parse_result.fail ._ _ expected :=
  parse_result.fail _  pos (dlist.lazy_of_list (msgs ()))
| ok := ok
end

/-- Overrides the expected token name, and does not consume input on failure. -/
def decorate_error (msg : thunk string) (p : parser elem α) : parser elem α :=
decorate_errors [msg ()] p

/-- Matches a single character satisfying the given predicate. -/
def sat (p : elem → Prop) [decidable_pred p] : parser elem elem :=
λ input pos,
if h : pos < input.size then
  let c := input.read ⟨pos, h⟩ in
  if p c then
    parse_result.done (pos+1) $ input.read ⟨pos, h⟩
  else
    parse_result.fail _ pos dlist.empty
else
  parse_result.fail _ pos dlist.empty

/-- Matches the empty word. -/
def eps : parser elem unit := return ()

/-- Matches the given character. -/
def el [decidable_eq elem] [has_to_string elem] (e : elem) : parser elem unit :=
decorate_error (to_string e) $ sat (= e) >> eps

/-- Matches a whole char_buffer.  Does not consume input in case of failure. -/
def buf [decidable_eq elem] [has_to_string elem] (buf : buffer elem) : parser elem unit :=
decorate_error (to_string buf) $ buf.to_list.mmap' el

/-- Matches one out of a list of characters. -/
def one_of [decidable_eq elem] [has_to_string elem] (cs : list elem) : parser elem elem :=
decorate_errors (do c ← cs, return (to_string c)) $
sat (∈ cs)

def one_of' [decidable_eq elem] [has_to_string elem] (cs : list elem) : parser elem unit :=
one_of cs >> eps

/-- Number of remaining input characters. -/
def remaining : parser elem ℕ :=
λ input pos, parse_result.done pos (input.size - pos)

/-- Matches the end of the input. -/
def eof : parser elem unit :=
decorate_error "<end-of-file>" $
do rem ← remaining, guard $ rem = 0

def foldr_core (f : α → β → β) (p : parser elem α) (b : β) : ∀ (reps : ℕ), parser elem β
| 0 := failure
| (reps+1) := (do x ← p, xs ← foldr_core reps, return (f x xs)) <|> return b

/-- Matches zero or more occurrences of `p`, and folds the result. -/
def foldr (f : α → β → β) (p : parser elem α) (b : β) : parser elem β :=
λ input pos, foldr_core f p b (input.size - pos + 1) input pos

def foldl_core (f : α → β → α) : ∀ (a : α) (p : parser elem β) (reps : ℕ), parser elem α
| a p 0 := failure
| a p (reps+1) := (do x ← p, foldl_core (f a x) p reps) <|> return a

/-- Matches zero or more occurrences of `p`, and folds the result. -/
def foldl (f : α → β → α) (a : α) (p : parser elem β) : parser elem α :=
λ input pos, foldl_core f a p (input.size - pos + 1) input pos

def choice (ps : list (parser elem α)) : parser elem α :=
  ps.foldr (<|>) failure

/-- Matches zero or more occurrences of `p`. -/
def many (p : parser elem α) : parser elem (list α) :=
foldr list.cons p []

/-- Matches zero or more occurrences of `p`. -/
def many' (p : parser elem α) : parser elem unit :=
many p >> eps

/-- Matches one or more occurrences of `p`. -/
def many1 (p : parser elem α) : parser elem (list α) :=
list.cons <$> p <*> many p

def many_char1 (p : parser elem char) : parser elem string :=
list.as_string <$> many1 p

/-- Matches one or more occurrences of `p`, separated by `sep`. -/
def sep_by1 (sep : parser elem unit) (p : parser elem α) : parser elem (list α) :=
list.cons <$> p <*> many (sep >> p)

/-- Matches zero or more occurrences of `p`, separated by `sep`. -/
def sep_by (sep : parser elem unit) (p : parser elem α) : parser elem (list α) :=
sep_by1 sep p <|> return []

/-- An implementation of `try` from other parser combinator libraries,
    ensures that the parser does not consume input. -/
def try {elem α : Type u} (p : parser elem α) : parser elem α :=
λ input pos, match p input pos with
  | parse_result.fail ._ _ expected1 := parse_result.fail _ pos expected1
  | succ := succ
  end

def fix_core (F : parser elem α → parser elem α) : ∀ (max_depth : ℕ), parser elem α
| 0             := failure
| (max_depth+1) := F (fix_core max_depth)

/-- Fixpoint combinator satisfying `fix F = F (fix F)`. -/
def fix (F : parser elem α → parser elem α) : parser elem α :=
λ input pos, fix_core F (input.size - pos + 1) input pos

def fix_core_fn {β : Type} (F : (β → parser elem α) → (β → parser elem α)) : ∀ (max_depth : ℕ), β → parser elem α
| 0             a := failure
| (max_depth+1) a := F (fix_core_fn max_depth) a

/-- Fixpoint combinator satisfying `fix F = F (fix F)`. -/
def fix_fn {β : Type} (F : (β → parser elem α) → (β → parser elem α)) : β → parser elem α :=
λ a input pos, fix_core_fn F (input.size - pos + 1) a input pos

private def make_monospaced : char → char
| '\n' := ' '
| '\t' := ' '
| '\x0d' := ' '
| c := c

def mk_error_msg {elem : Type} [has_to_string elem] (input : buffer elem) (pos : ℕ) (expected : dlist string) : char_buffer :=
let left_ctx := (input.take pos).take_right 10,
    right_ctx := (input.drop pos).take 10 in
(to_string left_ctx).to_char_buffer ++ (to_string right_ctx).to_char_buffer ++ "\n".to_char_buffer ++
/- left_ctx.map (λ _, ' ') ++ -/ "^\n".to_char_buffer ++
"\n".to_char_buffer ++
"expected: ".to_char_buffer
  ++ string.to_char_buffer (" | ".intercalate expected.to_list)
  ++ "\n".to_char_buffer

/-- Runs a parser on the given input.  The parser needs to match the complete input. -/
def run [has_to_string elem] (p : parser elem α) (input : buffer elem) : sum string α :=
match (p <* eof) input 0 with
| parse_result.done pos res := sum.inr res
| parse_result.fail ._ pos expected :=
  sum.inl $ (mk_error_msg input pos expected).to_string
end

end parser
