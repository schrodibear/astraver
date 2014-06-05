open Jc_env
open Jc_fenv
open Jc_ast
open Jc_pervasives
open Jc_constructors

let invoke_static : 'a. < .. > -> < .. > -> string -> 'a = fun o e name ->
  let open CamlinternalOO in
  let tag = public_method_label name in
  let obj : obj = Obj.magic o in
  let closure = get_public_method obj tag in
  let closure : 'a. < .. > -> 'a = Obj.magic closure in
  closure e

class positioned_wrapper o p : positioned =
object
  method pos = invoke_static o p "pos"
end

class id_wrapper o id : identifier =
object
  inherit positioned_wrapper o id
  method name = invoke_static o id "name"
end

let iwrap = new id_wrapper (new identifier "")

class typed_wrapper o p : typed =
object
  method typ = invoke_static o p "typ"
end

class labeled_wrapper o l : labeled =
object
  method label = invoke_static o l "label"
  method set_label = invoke_static o l "set_label"
end

class marked_wrapper o m : marked =
object
  (* method mark = unsafe_call m "mark" *)
  method mark = "" (* due to Jc_output implementation, which re-constructs the object in case the label in non-empty *)
end

class regioned_wrapper o r : regioned =
object
  method region = invoke_static o r "region"
  method set_region = invoke_static o r "set_region"
end

let pat_dummy = new pattern ~typ:JCTnull JCPany

class pat_wrapper o p : pattern =
  let wrap = new pat_wrapper pat_dummy in
object
  inherit positioned_wrapper o p
  inherit typed_wrapper o p
  method node = match invoke_static o p "node" with
    | JCPvar _ | JCPany |  JCPconst _ as p -> p
    | JCPstruct (si, l) ->    JCPstruct (si, List.map (fun (fi, p) -> fi, wrap p) l)
    | JCPor (p1, p2)    ->    JCPor (wrap p1, wrap p2)
    | JCPas (p, vi)     ->    JCPas (wrap p, vi)
end

let pwrap = new pat_wrapper pat_dummy

let term_dummy = Term.mkint ~value:0 ()

class term_wrapper o t : term =
  let wrap = new term_wrapper term_dummy in
object
  val mutable r = Jc_region.dummy_region
  inherit positioned_wrapper o t
  inherit typed_wrapper o t
  inherit labeled_wrapper o t
  inherit marked_wrapper o t
  inherit regioned_wrapper o t
  method node = match invoke_static o t "node" with
    | JCTconst _ | JCTvar _ as t -> t
    | JCTshift (t1, t2)       ->   JCTshift (wrap t1, wrap t2)
    | JCTderef (t, lab, fi)   ->   JCTderef (wrap t, lab, fi)
    | JCTbinary (t1, op, t2)  ->   JCTbinary (wrap t1, op, wrap t2)
    | JCTunary (op, t)        ->   JCTunary (op, wrap t)
    | JCTapp app              ->   JCTapp { app with jc_app_args = List.map wrap app.jc_app_args }
    | JCTold t                ->   JCTold (wrap t)
    | JCTat (t, lab)          ->   JCTat (wrap t, lab)
    | JCToffset (ok, t, si)   ->   JCToffset (ok, wrap t, si)
    | JCTaddress (ak, t)      ->   JCTaddress (ak, wrap t)
    | JCTbase_block t         ->   JCTbase_block (wrap t)
    | JCTinstanceof (t, lab, si) -> JCTinstanceof (wrap t, lab, si)
    | JCTcast (t, lab, si)    ->   JCTcast (wrap t, lab, si)
    | JCTbitwise_cast (t, lab, si) -> JCTbitwise_cast (wrap t, lab, si)
    | JCTrange_cast (t, ei)   ->   JCTrange_cast (wrap t, ei)
    | JCTreal_cast (t, rc)    ->   JCTreal_cast (wrap t, rc)
    | JCTif (ti, tt, te)      ->   JCTif (wrap ti, wrap tt, wrap te)
    | JCTrange (top1, top2)   ->   JCTrange (Option_misc.map wrap top1, Option_misc.map wrap top2)
    | JCTlet (vi, t1, t2)     ->   JCTlet (vi, wrap t1, wrap t2)
    | JCTmatch (t, l)         ->   JCTmatch (wrap t, List.map (fun (p, t) -> pwrap p, wrap t) l)
end

let twrap = new term_wrapper term_dummy

class tag_wrapper o tg : tag =
object
  inherit positioned_wrapper o tg
  method node = match invoke_static o tg "node" with
    | JCTtypeof (t, si) -> JCTtypeof (twrap t, si)
    | JCTtag _ | JCTbottom as t -> t
end

let tgwrap : tag -> tag = new tag_wrapper (new tag JCTbottom)

let assn_dummy = Assertion.mktrue ()

class assn_wrapper o (a : assertion) : assertion =
  let wrap = new assn_wrapper assn_dummy in
object
  inherit positioned_wrapper o a
  inherit labeled_wrapper o a
  inherit marked_wrapper o a
  method node =
    let wrap_trigger = function
      | JCAPatT t -> JCAPatT (twrap t)
      | JCAPatP a -> JCAPatP (wrap a)
    in
    match invoke_static o a "node" with
      | JCAtrue | JCAfalse as a ->            a
      | JCArelation (t1, op, t2) ->           JCArelation (twrap t1, op, twrap t2)
      | JCAand l ->                           JCAand (List.map wrap l)
      | JCAor l ->                            JCAor (List.map wrap l)
      | JCAimplies (a1, a2) ->                JCAimplies (wrap a1, wrap a2)
      | JCAiff (a1, a2) ->                    JCAiff  (wrap a1, wrap a2)
      | JCAnot a ->                           JCAnot (wrap a)
      | JCAapp app ->                         JCAapp { app with jc_app_args = List.map twrap app.jc_app_args }
      | JCAquantifier (q, vi, tl, a) ->       JCAquantifier (q, vi, List.map (List.map wrap_trigger) tl, wrap a)
      | JCAold a ->                           JCAold (wrap a)
      | JCAat (a, lab) ->                     JCAat (wrap a, lab)
      | JCAinstanceof (t, lab, si) ->         JCAinstanceof (twrap t, lab, si)
      | JCAbool_term t ->                     JCAbool_term (twrap t)
      | JCAfresh t ->                         JCAfresh (twrap t)
      | JCAif (t, a1, a2) ->                  JCAif (twrap t, wrap a1, wrap a2)
      | JCAmutable (t, si, tag) ->            JCAmutable (twrap t, si, tgwrap tag)
      | JCAeqtype (tag1, tag2, sio) ->        JCAeqtype (tgwrap tag1, tgwrap tag2, sio)
      | JCAsubtype (tag1, tag2, sio) ->       JCAsubtype (tgwrap tag1, tgwrap tag2, sio)
      | JCAlet (vi, t, a) ->                  JCAlet (vi, twrap t, wrap a)
      | JCAmatch (t, l) ->                    JCAmatch (twrap t, List.map (fun (p, a) -> pwrap p, wrap a) l)
end

let awrap = new assn_wrapper assn_dummy

let locs_dummy = new location_set ~typ:JCTnull @@ JCLSvar (newvar JCTnull)

class locs_wrapper o ls : location_set =
  let wrap = new locs_wrapper locs_dummy in
object
  val mutable r = Jc_region.dummy_region
  inherit positioned_wrapper o ls
  inherit typed_wrapper o ls
  inherit labeled_wrapper o ls
  inherit regioned_wrapper o ls
  method node = match invoke_static o ls "node" with
    | JCLSvar _ as ls -> ls
    | JCLSderef (ls, lab, fi, r) ->       JCLSderef (wrap ls, lab, fi, r)
    | JCLSrange (ls, topt1, topt2) ->     JCLSrange (wrap ls, Option_misc.map twrap topt1, Option_misc.map twrap topt2)
    | JCLSrange_term (t, topt1, topt2) ->
      JCLSrange_term (twrap t, Option_misc.map twrap topt1, Option_misc.map twrap topt2)
    | JCLSat (ls, lab) ->                 JCLSat (wrap ls, lab)
end

let lswrap : location_set -> location_set = new locs_wrapper locs_dummy

let loc_dummy = new location ~typ:JCTnull @@ JCLvar (newvar JCTnull)

class loc_wrapper o l : location =
  let wrap = new loc_wrapper loc_dummy in
object
  val mutable r = Jc_region.dummy_region
  inherit positioned_wrapper o l
  inherit typed_wrapper o l
  inherit labeled_wrapper o l
  inherit regioned_wrapper o l
  method node = match invoke_static o l "node" with
    | JCLvar _ as l -> l
    | JCLderef (ls, lab, fi, r) ->  JCLderef (lswrap ls, lab, fi, r)
    | JCLderef_term (t, fi) ->      JCLderef_term (twrap t, fi)
    | JCLat (l, lab) ->             JCLat (wrap l, lab)
end

let lwrap = new loc_wrapper loc_dummy

let expr_dummy = Expr.mk JCTnull (JCEconst JCCnull) ()

class expr_wrapper o e : expr =
  let wrap = new expr_wrapper expr_dummy in
object
  val mutable r = Jc_region.dummy_region
  inherit positioned_wrapper o e
  inherit typed_wrapper o e
  inherit marked_wrapper o e
  inherit regioned_wrapper o e
  method original_type = invoke_static o e "original_type" 
  method node = match invoke_static o e "node" with
    | JCEconst _ | JCEvar _ | JCEreturn_void as e -> e
    | JCEderef (e, fi) ->            JCEderef (wrap e, fi)
    | JCEbinary (e1, op, e2) ->      JCEbinary (wrap e1, op, wrap e2)
    | JCEunary (op, e) ->            JCEunary (op, wrap e)
    | JCEapp c ->                    JCEapp { c with jc_call_args = List.map wrap c.jc_call_args }
    | JCEassign_var (v, e) ->        JCEassign_var (v, wrap e)
    | JCEassign_heap (es, fi, eo) -> JCEassign_heap (wrap es, fi, wrap eo)
    | JCEinstanceof (e, si) ->       JCEinstanceof (wrap e, si)
    | JCEcast (e, si) ->             JCEcast (wrap e, si)
    | JCEbitwise_cast (e, si) ->     JCEbitwise_cast (wrap e, si)
    | JCErange_cast (e, ei) ->       JCErange_cast (wrap e, ei)
    | JCEreal_cast (e, rc) ->        JCEreal_cast (wrap e, rc)
    | JCEif (ei, et, ee) ->          JCEif (wrap ei, wrap et, wrap ee)
    | JCEoffset (ok, e, si) ->       JCEoffset (ok, wrap e, si)
    | JCEaddress (ak, e) ->          JCEaddress (ak, wrap e)
    | JCEbase_block e ->             JCEbase_block (wrap e)
    | JCEalloc (e, si) ->            JCEalloc (wrap e, si)
    | JCEfree e ->                   JCEfree (wrap e)
    | JCEreinterpret (e, si) ->      JCEreinterpret (wrap e, si)
    | JCEfresh e ->                  JCEfresh (wrap e)
    | JCElet (vi, eo, e) ->          JCElet (vi, Option_misc.map wrap eo, wrap e)
    | JCEassert (il, ak, a) ->       JCEassert (List.map iwrap il, ak, awrap a)
    | JCEcontract (ao, tioo, vi, psbl, e) ->
      JCEcontract (Option_misc.map awrap ao,
                   Option_misc.map (fun (t, io) -> twrap t, Option_misc.map iwrap io) tioo,
                   vi,
                   ListLabels.map psbl ~f:(fun (p, s, b) ->
                     p, s, { b with jc_behavior_assumes = Option_misc.map awrap b.jc_behavior_assumes;
                                    jc_behavior_assigns =
                                      Option_misc.map (fun (p, ll) -> p, List.map lwrap ll) b.jc_behavior_assigns;
                                    jc_behavior_allocates =
                                      Option_misc.map (fun (p, ll) -> p, List.map lwrap ll) b.jc_behavior_allocates;
                                    jc_behavior_ensures = awrap b.jc_behavior_ensures;
                                    jc_behavior_free_ensures = awrap b.jc_behavior_free_ensures }),
                   wrap e)
    | JCEblock elist ->              JCEblock (List.map wrap elist)
    | JCEloop (la, e) ->
      JCEloop ( { la with jc_loop_behaviors = ListLabels.map la.jc_loop_behaviors ~f:(fun (il, ao, llo) ->
                                                                                 List.map iwrap il,
                                                                                 Option_misc.map awrap ao,
                                                                                 Option_misc.map (List.map lwrap) llo);
                          jc_free_loop_invariant = awrap la.jc_free_loop_invariant;
                          jc_loop_variant = Option_misc.map (fun (t, lio) -> twrap t, lio) la.jc_loop_variant },
                wrap e)
    | JCEreturn (ty, e) ->           JCEreturn (ty, wrap e)
    | JCEtry (e1, l, e2) ->          JCEtry (wrap e1, List.map (fun (ei, vi, e) -> ei, vi, wrap e) l, wrap e2)
    | JCEthrow (ei, eo) ->           JCEthrow (ei, Option_misc.map wrap eo)
    | JCEpack (si1, e, si2) ->       JCEpack (si1, wrap e, si2)
    | JCEunpack (si1, e, si2) ->     JCEunpack (si1, wrap e, si2)
    | JCEmatch (e, pel) ->           JCEmatch (wrap e, List.map (fun (p, e) -> pwrap p, wrap e) pel)
    | JCEshift (e1, e2) ->           JCEshift (wrap e1, wrap e2)
end

let ewrap : expr -> expr = new expr_wrapper expr_dummy

let expr fmt e = Jc_output.expr fmt @@ ewrap e
let term fmt t = Jc_output.term fmt @@ twrap t
let assertion fmt a = Jc_output.assertion fmt @@ awrap a