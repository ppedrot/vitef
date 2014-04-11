#use "topfind";;
#require "unix";;

open Unix

let coqbin =
  try Sys.getenv "COQBIN"
  with Not_found -> ""

let buf = String.create 1024

let _ =
  let s = socket PF_INET SOCK_STREAM 0 in
  let () = setsockopt s SO_REUSEADDR true in
  let addr = ADDR_INET (inet_addr_loopback, 5555) in
  let () = connect s addr in
  let fd = s in
  while true do
    let read = read fd buf 0 1024 in
    if read = 0 then exit 0;
    ignore (write stdout buf 0 read)
  done;
  exit 0
