#!/usr/bin/env ocamlscript
Ocaml.ocamlflags := ["-thread"; "-no-alias-deps"];
Ocaml.packs := ["async"; "str"; "core_extended"];
Ocaml.sources := ["script_utils_async.ml"]
--

open Core.Std
open Core_extended
open Async.Std

open Script_utils_async

type config = {
  tests : string list;
  ncores : int;
  write : _to:[`err | `out] -> ?append:bool -> string -> unit Deferred.t
}

let _ : unit Deferred.t =
  let config =
    let ncores = ref 4 in
    let test_fname = ref "" in
    let usage =
      "Usage: test.ml test_file\n" ^
      "Jesssie regression tester (concurrent version). " ^
      "The test_file should contatin the list of .c files for replaying " ^
      "with Jessie/Why3 replay.\nOptions:"
    in
    let spec = ["-j", Arg.Int ((:=) ncores), "n Set number of workers to n"] in
    Arg.parse spec ((:=) test_fname) usage;
    if !test_fname = "" then begin
      Arg.usage spec usage;
      exit 2
    end else
      let write ~_to =
        write_file @@ !test_fname ^
        match _to with
        | `out -> ".out"
        | `err -> ".err"
      in
      input_lines (`filename !test_fname) >>| fun tests ->
      { tests;
        ncores = !ncores;
        write }
  in
  config >>= fun { tests; ncores = max_concurrent_jobs; write } ->
  let ntests = List.length tests in
  let throttle = Throttle.create ~continue_on_error:false ~max_concurrent_jobs in
  let time = Std.Unix.strftime Unix.(localtime @@ gettimeofday ()) "%d.%m.%Y at %H:%M:%S" in
  pr "Running on %d test(s) (started on %s):\n\n%!" ntests time;
  write ~_to:`out (spr "%d test(s) outputs (testing started on %s):\n\n%!" ntests time) >>= fun () ->
  write ~_to:`err (spr "%d test(s) errors (testing started on %s):\n\n%!" ntests time) >>= fun () ->
  List.map tests
    ~f:(fun filename ->
        Throttle.enqueue throttle @@ fun () ->
        Process.create ~prog:"frama-c" ~args:["-jessie"; "-jessie-atp"; "why3autoreplay"; filename] () >>=
        function
        | Result.Error e -> Deferred.return @@ `Failure (("", Error.to_string_hum e))
        | Result.Ok framac ->
          input_lines (`out framac) >>= fun outs ->
          input_lines ~rev:true (`err framac) >>| fun rev_errs ->
          let result =
            let concat = String.concat ~sep:"\n" in
            concat outs, concat @@ List.rev rev_errs
          in
          match outs, rev_errs with
          | _ :: _, "Session is not obsolete, hence not replayed" :: _ -> `Ok result
          | (_ :: _ as outs), errs
            when List.exists outs (matches (re ".*(replay OK.*)")) &&
                 List.for_all errs (matches (re "\\(\\[Config\\]\\|\\[Warning\\]\\).*")) ->
            `Ok' result
          | _, _ :: _ -> `Error result
          | _ -> `Failure result)
  |>
  List.fold2_exn
    tests
    ~init:(Deferred.return (0, 0))
    ~f:(fun acc filename result ->
        acc >>= fun (nsucc, nfail as acc) ->
        let header ~suffix = spr "%4d %-64s" (nsucc + nfail + 1) (filename ^ suffix) in
        pr "%s%!" @@ header ~suffix:"...";
        result >>= fun result ->
        let finish_with ~result:(outs, errs) ~color ~success s =
          write ~append:true ~_to:`out (spr "%s\n%s\n" (header ~suffix:":") outs) >>= fun () ->
          write ~append:true ~_to:`err (spr "%s\n%s\n" (header ~suffix:":") errs) >>| fun () ->
          pr "[%s]\n%!" @@ Color_print.color ~color s;
          Tuple.T2.(if success then map1 else map2) succ acc
        in
        match result with
        | `Ok result -> finish_with ~success:true ~result ~color:`Green "OK"
        | `Ok' result -> finish_with ~success:true ~result ~color:`Cyan "OK*"
        | `Error result -> finish_with ~success:false ~result ~color:`Red "ERROR"
        | `Failure result -> finish_with ~success:false ~result ~color:`Purple "FAILURE")
  >>| fun (nsucc, nfail) ->
  assert (nsucc + nfail = ntests);
  pr "\nCompleted %d test(s): %s successful, %s failed\n%!"
    (nsucc + nfail)
    (Color_print.green @@ string_of_int nsucc)
    (Color_print.red @@ string_of_int  nfail);
  shutdown 0

let () = never_returns @@ Scheduler.go ()
