open Termops
open Entries
open Environ
open Context
open Namegen
open Evarutil
open Refiner
open Tacmach
open Tactics

let interpretable_as_section_decl d1 d2 = match d1,d2 with
  | (_,Some _,_), (_,None,_) -> false
  | (_,Some b1,t1), (_,Some b2,t2) -> eq_constr b1 b2 & eq_constr t1 t2
  | (_,None,t1), (_,_,t2) -> eq_constr t1 t2

let abstract id tac gl =
  try
    let current_sign = Global.named_context () in
    let global_sign = pf_hyps gl in
    let fold (id,_,_ as d) (s1, s2) =
          if mem_named_context id current_sign &&
            interpretable_as_section_decl (lookup_named id current_sign) d
          then (s1,push_named_context_val d s2)
          else (add_named_decl d s1,s2)
    in
    let sign, secsign = List.fold_right
      fold global_sign (empty_named_context,empty_named_context_val) in
    let id = next_global_ident_away id (pf_ids_of_hyps gl) in
    let concl = it_mkNamedProd_or_LetIn (pf_concl gl) sign in
    let concl = flush_and_check_evars (project gl) concl in
    let rtac = tclCOMPLETE (tclTHEN (tclDO (List.length sign) intro) tac) in
    let const = Pfedit.build_constant_by_tactic id secsign concl rtac in
    Some const.const_entry_body
  with _ -> None

let fork (f : unit -> 'a) =
  let pipe_in, pipe_out = Unix.pipe () in
  let pid = Unix.fork () in
  if pid = 0 then
    let out_chan = Unix.out_channel_of_descr pipe_out in
    let data = f () in
    let () = Marshal.to_channel out_chan data [] in
    let () = close_out out_chan in
    exit 0
  else
    (pid, pipe_in)

let spawn (process : (unit -> 'a) list) : 'a list =
  let fresh f =
    let (pid, chan) = fork f in
    (chan, (pid, Buffer.create 64))
  in
  let buffer = String.create 1024 in
  let count = ref (List.length process) in
  let process = List.map fresh process in
  let (chans, _) = List.split process in
  let rec loop () =
    if !count = 0 then ()
    else
      let id, _ = Unix.waitpid [Unix.WNOHANG] 0 in
      if id = 0 then
        let (readable, _, _) = Unix.select chans [] [] 0.1 in
        let iter chan =
          let (_, buf) = List.assoc chan process in
          let len = Unix.read chan buffer 0 1024 in
          let () = Buffer.add_substring buf buffer 0 len in
          ()
        in
        let () = List.iter iter readable in
        loop ()
      else
        let find (_, (pid, _)) = id = pid in
        let () = if List.exists find process then decr count in
        loop ()
  in
  let () = loop () in
  let map (chan, (_, buf)) =
    let () = Unix.close chan in
    let str = Buffer.contents buf in
    Marshal.from_string str 0
  in
  List.map map process

let fork_tac init tac gl =
  let init = Tacinterp.eval_tactic init in
  let state = init gl in
  let gls = Evd.sig_it state in
  let evd = Evd.sig_sig state in
  let tac = Tacinterp.eval_tactic tac in
  let process gl = (); fun () ->
    let gl = { Evd.it = gl; sigma = evd } in
    let id = Names.Id.of_string "__fork__" in
    abstract id tac gl
  in
  let data = spawn (List.map process gls) in
  let fold gl cstr (gls, evd) = match cstr with
  | None -> (gl :: gls, evd)
  | Some c ->
    let goal = { Evd.it = gl; Evd.sigma = evd; } in
    let ans = exact_no_check c goal in
    let () = assert (CList.is_empty ans.Evd.it) in
    gls, ans.Evd.sigma
  in
  let (gls, evd) = List.fold_right2 fold gls data ([], evd) in
  { Evd.it = gls; Evd.sigma = evd }
