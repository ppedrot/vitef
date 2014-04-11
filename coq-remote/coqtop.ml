#use "topfind";;
#require "unix";;

open Unix

let coqbin =
  try Sys.getenv "COQBIN"
  with Not_found -> ""

let port =
  try int_of_string Sys.argv.(1)
  with _ ->
    Printf.eprintf "No port specified\n%!";
    exit 1

let buf = String.create 1024

let _ =
  let s = socket PF_INET SOCK_STREAM 0 in
  let () = setsockopt s SO_REUSEADDR true in
  let () = bind s (ADDR_INET (inet_addr_any, port)) in
  let () = listen s 1 in
  let fd, _ = accept s in
  while true do
    let _, _, _ = select [fd] [] [] (-1.) in
    let read = read fd buf 0 1024 in
    if read = 0 then exit 0;
    ignore (write stdout buf 0 read)
  done;
  exit 0
