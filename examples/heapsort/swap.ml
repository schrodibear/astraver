
let swap =
  fun (N:int)(t:array N of int)(i,j:int) ->
    { 0 <= i < N and 0 <= j < N }
    (let v = t[i] in
     begin
       t[i] := t[j];
       t[j] := v
     end)
    { exchange(t, t@, i, j) }
