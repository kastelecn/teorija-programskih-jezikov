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
      in
      begin match f with
      | S.Lambda (x, e) -> eval_exp (S.subst [(x, e2)] e)
      | S.RecLambda (f, x, e) as rec_f -> eval_exp (S.subst [(f, rec_f); (x, e2)] e)
      | _ -> failwith "Function expected"
      end
    | S.Pair (e1,e2) -> S.Pair (eval_exp e1, eval_exp e2)
    | S.Fst e -> begin
        match e with
        |S.Pair (e1,e2) -> eval_exp e1
        | _ -> failwith "Pair expected!"
        end
    | S.Snd e -> begin
        match e with
        |S.Pair (e1,e2) -> eval_exp e2
        | _ -> failwith "Pair expected!"
        end
    | S.Nil -> S.Nil
    | S.Cons(x,xs) -> S.Cons(eval_exp x, eval_exp xs)
    | S.Match (e, e1, x, xs, e2) ->
          begin match eval_exp e with
              |S.Nil -> eval_exp e1
              |S.Cons (y,ys) -> eval_exp (S.subst [(x,y); (xs,ys)] e2)
              | _ -> failwith "List expected"
    end

    
and eval_int e =
  match eval_exp e with
  | S.Int n -> n
  | _ -> failwith "Integer expected"

  let rec is_value = function
  | S.Int _ | S.Bool _ | S.Lambda _ | S.Nil | S.RecLambda _ -> true
  | S.Var _ | S.Plus _ | S.Minus _ | S.Times _ | S.Equal _ | S.Less _ | S.Greater _
  | S.IfThenElse _ | S.Apply _  | S.Match _  -> false
  | S.Pair (e1, e2) -> is_value e1 && is_value e2
  | S.Cons (y,ys) -> is_value y && is_value ys
  | S.Fst e -> begin
    match e with
    | S.Pair (e1,e2) -> is_value e1
    |_ -> failwith "Pair expected"
    end
  | S.Snd e -> begin
    match e with
    | S.Pair (e1,e2) -> is_value e2
    |_ -> failwith "Pair expected"
    end

let rec step = function
  | S.Var _ | S.Int _ | S.Bool _ | S.Lambda _ | S.RecLambda _ -> failwith "Expected a non-terminal expression"
  | S.Pair (a, b) when (is_value a && is_value b) -> failwith "Expected a non-terminal expression"
  | S.Cons (a, b) when (is_value a && is_value b) -> failwith "Expected a non-terminal expression"
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
  | S.Match (e,e1,x,xs,e2) ->  begin
    match is_value e with
    |true ->  begin match e with
      |S.Nil ->  begin match is_value e1 with
        |true ->  e1
        |false -> S.Match (e,step e1,x,xs,e2)
        end
      |S.Cons(y,ys) -> begin match is_value e2 with
        |true ->  e2
        |false ->S.Match (e,e1,x,xs,step (S.subst [(x,y); (xs,ys)] e2))
        end
      |_ -> failwith "List expected"
      end
    |false -> S.Match (step e,e1,x,xs,e2)
    end
  | S.Pair (e1,e2) -> begin
    match is_value e1, is_value e2 with
    | true, false -> S.Pair (e1,step e2)
    | false, _ -> S.Pair (step e1, e2)
    end
  | S.Fst e -> if (is_value (S.Fst e)) then S.Fst e else S.Fst (step e)
  | S.Snd e -> if (is_value (S.Snd e)) then S.Snd e else S.Snd (step e)
  | S.Cons (x,xs) -> if is_value x then S.Cons(x, step xs) else S.Cons (step x, xs)

let big_step e =
  let v = eval_exp e in
  print_endline (S.string_of_exp v)

let rec small_step e =
  print_endline (S.string_of_exp e);
  if not (is_value e) then
    (print_endline "  ~>";
    small_step (step e))
