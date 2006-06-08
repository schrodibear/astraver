open Options

let queue = Queue.create ()

let reset =
  match types_encoding with
    NoEncoding -> (fun () -> Queue.clear queue)
  | Predicates -> Encoding_pred.reset
  | Stratified -> Encoding_strat.reset
  | Recursive -> Encoding_rec.reset

let push =
  match types_encoding with
    NoEncoding -> (fun d -> Queue.add d queue)
  | Predicates -> Encoding_pred.push
  | Stratified -> Encoding_strat.push
  | Recursive -> Encoding_rec.push

let iter =
  match types_encoding with
    NoEncoding -> (fun f -> Queue.iter f queue)
  | Predicates -> Encoding_pred.iter
  | Stratified -> Encoding_strat.iter
  | Recursive -> Encoding_rec.iter
