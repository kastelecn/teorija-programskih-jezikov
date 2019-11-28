module S = Syntax


let rec eval_exp = function
  | S.Var x -> failwith "Expected a closed term"
  | S.Int _ | S.Bool _ | S.Lambda _ | S.RecLambda _ as e -> e
  | S.Plus (e1, e2) ->
      let n1 = eval_int e1
      and n2 = eval_int e2
      in S.Int (n1 + n2)
  | S.Minus (e1, e2) ->
      let n1 = eval_int e1
      and n2 = eval_int e2
      in S.Int (n1 - n2)
  | S.Times (e1, e2) ->
      let n1 = eval_int e1
      and n2 = eval_int e2
      in S.Int (n1 * n2)
  | S.Equal (e1, e2) ->
      let n1 = eval_int e1
      and n2 = eval_int e2
      in S.Bool (n1 = n2)
  | S.Less (e1, e2) ->
      let n1 = eval_int e1
      and n2 = eval_int e2
      in S.Bool (n1 < n2)
  | S.Greater (e1, e2) ->
      let n1 = eval_int e1
      and n2 = eval_int e2
      in S.Bool (n1 > n2)
  | S.IfThenElse (e, e1, e2) ->
      begin match eval_exp e with
      | S.Bool true -> eval_exp e1
      | S.Bool false -> eval_exp e2
      | _ -> failwith "Boolean expected"
      end
  | S.Apply (e1, e2) ->
      let f = eval_exp e1
      and v = eval_exp e2
      in
      begin match f with
      | S.Lambda (x, e) -> eval_exp (S.subst [(x, v)] e)
      | S.RecLambda (f, x, e) as rec_f -> eval_exp (S.subst [(f, rec_f); (x, v)] e)
      | _ -> failwith "Function expected"
      end
  | S.Pair (e1, e2) -> S.Pair(eval_exp e1, eval_exp e2)
  | S.Fst e1 -> S.Fst(eval_exp e1)
  | S.Snd e2 -> S.Snd(eval_exp e2)
  | S.Nil -> Nil
  | S.Cons (x, xs) -> S.Cons(eval_exp x, eval_exp xs)
  | S.Match (e, e1, x, xs, e2)-> begin match eval_exp e with
                                  |S.Nil -> eval_exp e1
                                  |S.Cons -> eval_exp e2
                                  |_ -> failwith "List expression"
    end
and eval_int e =
  match eval_exp e with
  | S.Int n -> n
  | _ -> failwith "Integer expected"

let rec is_value = function
  | S.Int _ | S.Bool _ | S.Lambda _ | S.Nil | S.RecLambda _ -> true
  | S.Var _ | S.Plus _ | S.Minus _ | S.Times _ | S.Equal _ | S.Less _ | S.Greater _
  | S.IfThenElse _ | S.Apply _ | S.Cons _ | S.Match _ |S.Fst _ | S.Dnd _ | S.Pair _ -> false
(*   | S.Fst e -> begin match e with
              |Pair (e1, e2) -> is_value e1 
              |_ -> failwith "Fst exeption"
  end
  | S.Snd e -> begin match e with
              |Pair (e1, e2) -> is_value e2 
              |_ -> failwith "Fst exeption"
  end
  | S.Pair (e1, e2) -> is_value e1 && is_value e2 *)

let rec step = function
  | S.Var _ | S.Int _ | S.Bool _ | S.Lambda _ | S.Nil | S.RecLambda _ -> failwith "Expected a non-terminal expression"
  | S.Plus (S.Int n1, S.Int n2) -> S.Int (n1 + n2)
  | S.Plus (S.Int n1, e2) -> S.Plus (S.Int n1, step e2)
  | S.Plus (e1, e2) -> S.Plus (step e1, e2)
  | S.Minus (S.Int n1, S.Int n2) -> S.Int (n1 - n2)
  | S.Minus (S.Int n1, e2) -> S.Minus (S.Int n1, step e2)
  | S.Minus (e1, e2) -> S.Minus (step e1, e2)
  | S.Times (S.Int n1, S.Int n2) -> S.Int (n1 * n2)
  | S.Times (S.Int n1, e2) -> S.Times (S.Int n1, step e2)
  | S.Times (e1, e2) -> S.Times (step e1, e2)
  | S.Equal (S.Int n1, S.Int n2) -> S.Bool (n1 = n2)
  | S.Equal (S.Int n1, e2) -> S.Equal (S.Int n1, step e2)
  | S.Equal (e1, e2) -> S.Equal (step e1, e2)
  | S.Less (S.Int n1, S.Int n2) -> S.Bool (n1 < n2)
  | S.Less (S.Int n1, e2) -> S.Less (S.Int n1, step e2)
  | S.Less (e1, e2) -> S.Less (step e1, e2)
  | S.Greater (S.Int n1, S.Int n2) -> S.Bool (n1 > n2)
  | S.Greater (S.Int n1, e2) -> S.Greater (S.Int n1, step e2)
  | S.Greater (e1, e2) -> S.Greater (step e1, e2)
  | S.IfThenElse (S.Bool b, e1, e2) -> if b then e1 else e2
  | S.IfThenElse (e, e1, e2) -> S.IfThenElse (step e, e1, e2)
  | S.Apply (S.Lambda (x, e), v) when is_value v -> S.subst [(x, v)] e
  | S.Apply (S.RecLambda (f, x, e) as rec_f, v) when is_value v -> S.subst [(f, rec_f); (x, v)] e
  | S.Apply ((S.Lambda _ | S.RecLambda _) as f, e) -> S.Apply (f, step e)
  | S.Apply (e1, e2) -> S.Apply (step e1, e2)
  | S.Pair (e1, e2) -> begin match is_value e1, is value e2 with
                        |true, true -> S.Pair (e1, e2)
                        |true, false -> S.Pair (e1, step e2)
                        |false, _ -> S.Pair (step e1, e2)
  | S.Fst e1 -> begin match e with
                  |Pair (e1, e2) ->if  is_value e1 then e1 else step e1
                  |_ -> failwith "Fst exeption"
            end
  | S.Snd e1 -> begin match e with
                  |Pair (e1, e2) ->if  is_value e2 then e2 else step e2
                  |_ -> failwith "Fst exeption"
end
  | S.Cons (x, xs) -> if is_value x then S.Cons (x, step xs) else S.Cons(step x, xs)
  | S.Match (e, e1, x, xs, e2)-> begin match e with
                                  |S.Nil -> step e1
                                  |S.Cons(x, xs) -> step e2
end
  
let big_step e =
  let v = eval_exp e in
  print_endline (S.string_of_exp v)

let rec small_step e =
  print_endline (S.string_of_exp e);
  if not (is_value e) then
    (print_endline "  ~>";
    small_step (step e))
