  import .core

  namespace parser
  namespace expr

  inductive assoc
  | none
  | left
  | right

  inductive operator (elem a : Type)
  | inf : parser elem (a → a → a) → assoc → operator
  | pre : parser elem (a → a) → operator
  | post : parser elem (a → a) → operator

  @[reducible] def op_table (elem a : Type) :=
  (list (parser elem (a → a → a)) ×
   list (parser elem (a → a → a)) ×
   list (parser elem (a → a → a)) ×
   list (parser elem (a → a)) ×
   list (parser elem (a → a)))

def op_table.empty {elem a : Type} : op_table elem a :=
([],[],[],[],[])

  def split_op {elem a : Type} : operator elem a → op_table elem a → op_table elem a
  | (operator.inf op assoc.none) (rassoc, lassoc, nassoc, pre, post) := (rassoc,lassoc,op::nassoc,pre,post)
  | (operator.inf op assoc.left) (rassoc, lassoc, nassoc, pre, post):= (rassoc, op::lassoc,nassoc,pre,post)
  | (operator.inf op assoc.right) (rassoc, lassoc, nassoc, pre, post):= (op::rassoc,lassoc,nassoc,pre,post)
  | (operator.pre op) (rassoc, lassoc, nassoc, pre, post) := (rassoc,lassoc,nassoc,op::pre,post)
  | (operator.post op) (rassoc, lassoc, nassoc, pre, post) := (rassoc,lassoc,nassoc,pre,op::post).

@[reducible] def operator_table (elem a : Type) := list $ list $ operator elem a

def ambigious {elem a b : Type} (assoc : string) (op : parser elem a) : parser elem b :=
parser.try $ do op, parser.fail $ "ambigous use of a " ++ assoc ++ " associative operator"

def rassoc_p' {elem a : Type}
    (rassoc_op : parser elem (a → a → a))
    (amb_left amb_non term_p : parser elem a)
    (x : a) : parser elem a :=
@parser.fix_fn elem a a (fun rassoc_p x,
let rassoc_p1 := fun (x : a), rassoc_p x <|> return x in
(do f ← rassoc_op,
   y ← (do z ← term_p, rassoc_p1 z),
   return (f x y)) <|> amb_left <|> amb_non) x


        --       lassocP x  = do{ f <- lassocOp
        --                      ; y <- termP
        --                      ; lassocP1 (f x y)
        --                      }
        --                    <|> ambigiousRight
        --                    <|> ambigiousNon
        --                    -- <|> return x

        --       lassocP1 x = lassocP x <|> return x
def lassoc_p' {elem a : Type}
    (lassoc_op : parser elem (a → a → a))
    (amb_right amb_non term_p : parser elem a)
    (x : a) : parser elem a :=
@parser.fix_fn elem a a (fun lassoc_p x,
let lassoc_p1 := fun (x : a), lassoc_p x <|> pure x in
(do f ← lassoc_op,
   y ← term_p,
   lassoc_p1 (f x y)) <|> amb_right <|> amb_non) x


private def make_parser {elem a : Type} (term : parser elem a) (ops : list $ operator elem a) : parser elem a :=
        let (rassoc, lassoc, nassoc, pre, post) := list.foldr split_op op_table.empty ops,
        rassoc_op := parser.choice rassoc,
        lassoc_op := parser.choice lassoc,
        nassoc_op := parser.choice nassoc,
        prefix_op := parser.choice pre, --  <?> ""
        postfix_op := parser.choice post, -- <?> ""
        ambigious_right := @ambigious _ _ a "right" rassoc_op,
        ambigious_left := @ambigious _ _ a "left" lassoc_op,
        ambigious_non  := @ambigious _ _ a"non" nassoc_op,
        prefix_p := prefix_op <|> return id,
        postfix_p := postfix_op <|> return id,
        term_p := (do pre <- prefix_p, x ← term, post ← postfix_p, return (post (pre x))),
        rassoc_p := rassoc_p' rassoc_op ambigious_left ambigious_non term_p,
        lassoc_p := lassoc_p' lassoc_op ambigious_right ambigious_non term_p,
        nassoc_p := (fun (x : a),
            (do f ← nassoc_op,
                y ← term_p,
                ambigious_right <|>
                ambigious_left <|>
                ambigious_non <|>
                pure (f x y)))
        in do x ← term_p, rassoc_p x <|> lassoc_p x <|> nassoc_p x <|> return x

def mk_expr_parser {elem a : Type} : operator_table elem a → parser elem a → parser elem a
| table simple_expr := table.foldl make_parser simple_expr

end expr
end parser
