(* The map the extracted checks call as KEngine.pmap: List.map, computed by
   forked children over contiguous chunks of the list, whose results come back
   marshalled through pipes and are joined in order. A chunk whose child fails
   is computed again by a new child, and after a second failure by the parent
   itself; each failure is reported on stderr with the item, the exception and
   the size of the heap, and each call with its size and time. A child's major
   collector copies the pages of the heap it shares with the parent, so a
   heap above 2 GiB is compacted before the fork and the number of children
   is capped by the available memory over the size of the heap. Inside a child
   every further pmap runs as List.map. *)
let nproc = ref 1
let inside = ref false
let calls = ref 0

let log fmt = Printf.ksprintf (fun s -> prerr_string s; flush stderr) fmt

let mem_available () =
  match open_in "/proc/meminfo" with
  | exception _ -> max_int
  | ic ->
    let res = ref max_int in
    (try while true do
       let line = input_line ic in
       (try Scanf.sscanf line "MemAvailable: %d kB" (fun k -> res := k * 1024) with _ -> ())
     done with End_of_file -> ());
    close_in ic;
    !res

let heap_bytes () = (Gc.quick_stat ()).Gc.heap_words * (Sys.word_size / 8)

let children call len =
  let k = min !nproc len in
  if k <= 1 then k
  else begin
    if heap_bytes () > 1 lsl 31 then Gc.compact ();
    let h = max (heap_bytes ()) 1 in
    let cap = max 1 (mem_available () / 5 * 4 / h) in
    if cap < k then log "pmap %d: heap %d MiB, %d children\n" call (h / 1048576) cap;
    min k cap
  end

let run_chunk call f arr a b =
  Array.init (b - a) (fun j ->
    try f arr.(a + j) with e ->
      let st = Gc.quick_stat () in
      log "pmap %d: item %d of [%d, %d) raised %s (heap %d words, top %d words)\n"
        call (a + j) a b (Printexc.to_string e) st.Gc.heap_words st.Gc.top_heap_words;
      raise e)

let spawn call f arr a b =
  let (rd, wr) = Unix.pipe () in
  match Unix.fork () with
  | 0 ->
    Unix.close rd;
    inside := true;
    (try
       let res = run_chunk call f arr a b in
       let oc = Unix.out_channel_of_descr wr in
       Marshal.to_channel oc res [];
       close_out oc;
       Unix._exit 0
     with e ->
       log "pmap %d: child for [%d, %d) failed: %s\n" call a b (Printexc.to_string e);
       Unix._exit 3)
  | pid -> Unix.close wr; (pid, rd)

let collect (pid, rd) =
  let ic = Unix.in_channel_of_descr rd in
  let res = (try Some (Marshal.from_channel ic) with _ -> None) in
  close_in ic;
  let ok = (match Unix.waitpid [] pid with (_, Unix.WEXITED 0) -> true | _ -> false) in
  if ok then res else None

let pmap (f : 'a -> 'b) (l : 'a list) : 'b list =
  let len = Stdlib.List.length l in
  if min !nproc len <= 1 || !inside then Stdlib.List.map f l
  else begin
    incr calls;
    let call = !calls in
    let arr = Array.of_list l in
    let k = children call len in
    let t0 = Unix.gettimeofday () in
    flush stdout; flush stderr;
    let bounds = Array.init k (fun i -> (i * len / k, (i + 1) * len / k)) in
    let kids = Array.map (fun (a, b) -> spawn call f arr a b) bounds in
    let parts = Array.mapi (fun i kid ->
      let (a, b) = bounds.(i) in
      match collect kid with
      | Some (res : 'b array) -> res
      | None ->
        log "pmap %d: chunk [%d, %d) failed; computing it again in a new child\n" call a b;
        (match collect (spawn call f arr a b) with
         | Some (res : 'b array) -> res
         | None ->
           log "pmap %d: chunk [%d, %d) failed again; computing it in the parent\n" call a b;
           run_chunk call f arr a b)) kids in
    log "pmap %d: %d items in %d chunks, %.1f s\n" call len k (Unix.gettimeofday () -. t0);
    Stdlib.List.concat (Stdlib.List.map Array.to_list (Array.to_list parts))
  end
