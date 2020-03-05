
type __ = Obj.t

(** val id : 'a1 -> 'a1 **)

let id x =
  x

(** val add : OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

let rec add = (+)

(** val mul : OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

let rec mul = ( * )

(** val ltb : OCamlNativeInt.t -> OCamlNativeInt.t -> bool **)

let ltb = (<)

module Nat =
 struct
  (** val ltb : OCamlNativeInt.t -> OCamlNativeInt.t -> bool **)

  let ltb n m =
    (<=) (Pervasives.succ n) m
 end

type cache =
| Build_Cache

type cacheFormat = __

type cacheDecode = __

type 't cacheAdd = { addE : (cacheFormat -> 't -> cacheFormat);
                     addD : (cacheDecode -> 't -> cacheDecode) }

(** val addE : cache -> 'a1 cacheAdd -> cacheFormat -> 'a1 -> cacheFormat **)

let addE _ x = x.addE

(** val addD : cache -> 'a1 cacheAdd -> cacheDecode -> 'a1 -> cacheDecode **)

let addD _ x = x.addD

type char = Int64Word.t



module ByteBuffer =
 struct
 end

type 's alignedEncodeM =
  (int list) -> OCamlNativeInt.t -> 's -> cacheFormat ->
  (((int list)*OCamlNativeInt.t)*cacheFormat) option

(** val alignedEncode_Nil : cache -> OCamlNativeInt.t -> 'a1 alignedEncodeM **)

let alignedEncode_Nil _ numBytes v idx _ env =
  if Nat.ltb idx (Pervasives.succ numBytes) then Some ((v,idx),env) else None

type 'a alignedDecodeM =
  (int list) -> OCamlNativeInt.t -> cacheDecode -> (('a*OCamlNativeInt.t)*cacheDecode) option



(** val setCurrentBytes :
    cache -> OCamlNativeInt.t cacheAdd -> OCamlNativeInt.t -> OCamlNativeInt.t ->
    Int64Word.t alignedEncodeM **)

let rec setCurrentBytes cache0 cacheAddNat n sz =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> alignedEncode_Nil cache0 n)
    (fun sz0 v idx w ce ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      if Nat.ltb idx n
      then Some
             ((((fun _ ->   let rec set_nth l i x =     match l, i with     | [], 0 -> [x]     | [], _ -> 0 :: set_nth [] (i-1) x     | _ :: l, 0 -> x :: l     | y :: l, _ -> y :: set_nth l (i-1) x in   set_nth)
                 n v idx w),(Pervasives.succ
             idx)),(cacheAddNat.addE ce (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ 0))))))))))
      else None)
      (fun _ ->
      if Nat.ltb idx n
      then let a =
             (((fun _ ->   let rec set_nth l i x =     match l, i with     | [], 0 -> [x]     | [], _ -> 0 :: set_nth [] (i-1) x     | _ :: l, 0 -> x :: l     | y :: l, _ -> y :: set_nth l (i-1) x in   set_nth)
                n v idx
                (Int64Word.split1' (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ 0))))))))
                  (mul sz0 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ 0))))))))) w)),(Pervasives.succ
             idx)),(cacheAddNat.addE ce (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ 0)))))))))
           in
           setCurrentBytes cache0 cacheAddNat n sz0 (let x,_ = let x,_ = a in x in x)
             (let _,y = let x,_ = a in x in y)
             (Int64Word.split2' (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ 0))))))))
               (mul sz0 (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 0))))))))) w) (let _,y = a in y)
      else None)
      sz0)
    sz

(** val test_cache : cache **)

let test_cache =
  Build_Cache

(** val test_cache_add_nat : OCamlNativeInt.t cacheAdd **)

let test_cache_add_nat =
  { addE = (fun ce _ -> ce); addD = (fun cd _ -> cd) }

(** val listAlignedDecodeM :
    cache -> OCamlNativeInt.t -> (OCamlNativeInt.t -> 'a1 alignedDecodeM) ->
    OCamlNativeInt.t -> 'a1 list alignedDecodeM **)

let rec listAlignedDecodeM cache0 m a_decode_align n x x0 x1 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some (([],x0),x1))
    (fun s' ->
    match a_decode_align m x x0 x1 with
    | Some a ->
      (match listAlignedDecodeM cache0 m a_decode_align s' x
               (let _,y = let x2,_ = a in x2 in y) (let _,y = a in y) with
       | Some a0 ->
         Some
           ((((let x2,_ = let x2,_ = a in x2 in x2) :: (let x2,_ = let x2,_ = a0 in x2 in x2)),
           (let _,y = let x2,_ = a0 in x2 in y)),(let _,y = a0 in y))
       | None -> None)
    | None -> None)
    n

(** val alignedEncodeList' :
    cache -> (OCamlNativeInt.t -> 'a1 alignedEncodeM) -> OCamlNativeInt.t -> (int list) ->
    OCamlNativeInt.t -> 'a1 list -> cacheFormat ->
    (((int list)*OCamlNativeInt.t)*cacheFormat) option **)

let rec alignedEncodeList' cache0 a_format_align sz v idx as0 env =
  match as0 with
  | [] -> if ltb idx (Pervasives.succ sz) then Some ((v,idx),env) else None
  | a :: as' ->
    (match a_format_align sz v idx a env with
     | Some a0 ->
       alignedEncodeList' cache0 a_format_align sz (let x,_ = let x,_ = a0 in x in x)
         (let _,y = let x,_ = a0 in x in y) as' (let _,y = a0 in y)
     | None -> None)

(** val alignedEncodeList :
    cache -> (OCamlNativeInt.t -> 'a1 alignedEncodeM) -> OCamlNativeInt.t -> 'a1 list
    alignedEncodeM **)

let alignedEncodeList =
  alignedEncodeList'

(** val wrapDecoder :
    OCamlNativeInt.t -> (OCamlNativeInt.t -> (int list) -> (('a1*OCamlNativeInt.t)*'a2)
    option) -> (int list) -> 'a1 option **)

let wrapDecoder sz impl bs =
  match impl sz bs with
  | Some p -> let p0,_ = p in let pkt,_ = p0 in Some pkt
  | None -> None

(** val wrapEncoder :
    OCamlNativeInt.t -> (OCamlNativeInt.t -> (int list) -> 'a1 ->
    (((int list)*OCamlNativeInt.t)*'a2) option) -> 'a1 -> (int list) -> (int list) option **)

let wrapEncoder sz impl pkt out =
  match impl sz out pkt with
  | Some p -> let p0,_ = p in let out0,_ = p0 in Some out0
  | None -> None

type hTTP_Frame = { length : Int64Word.t; type0 : Int64Word.t; flags : Int64Word.t;
                    r : Int64Word.t; stream_Identifier : Int64Word.t;
                    payload : Int64Word.t list }

(** val length : hTTP_Frame -> Int64Word.t **)

let length x = x.length

(** val type0 : hTTP_Frame -> Int64Word.t **)

let type0 x = x.type0

(** val flags : hTTP_Frame -> Int64Word.t **)

let flags x = x.flags

(** val r : hTTP_Frame -> Int64Word.t **)

let r x = x.r

(** val stream_Identifier : hTTP_Frame -> Int64Word.t **)

let stream_Identifier x = x.stream_Identifier

(** val payload : hTTP_Frame -> Int64Word.t list **)

let payload x = x.payload

(** val hTTP_Frame_encoder_impl :
    OCamlNativeInt.t -> (int list) -> hTTP_Frame ->
    (((int list)*OCamlNativeInt.t)*cacheFormat) option **)

let hTTP_Frame_encoder_impl sz v r0 =
  match setCurrentBytes test_cache test_cache_add_nat sz (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0))) v 0 r0.length (Obj.magic ()) with
  | Some a ->
    let idx = let _,y = let x,_ = a in x in y in
    if Nat.ltb idx sz
    then let a0 =
           (((fun _ ->   let rec set_nth l i x =     match l, i with     | [], 0 -> [x]     | [], _ -> 0 :: set_nth [] (i-1) x     | _ :: l, 0 -> x :: l     | y :: l, _ -> y :: set_nth l (i-1) x in   set_nth)
              sz (let x,_ = let x,_ = a in x in x) idx r0.type0),(Pervasives.succ
           idx)),(test_cache_add_nat.addE (let _,y = a in y) (Pervasives.succ
                   (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))
         in
         let idx0 = let _,y = let x,_ = a0 in x in y in
         if Nat.ltb idx0 sz
         then let a1 =
                (((fun _ ->   let rec set_nth l i x =     match l, i with     | [], 0 -> [x]     | [], _ -> 0 :: set_nth [] (i-1) x     | _ :: l, 0 -> x :: l     | y :: l, _ -> y :: set_nth l (i-1) x in   set_nth)
                   sz (let x,_ = let x,_ = a0 in x in x) idx0 r0.flags),(Pervasives.succ
                idx0)),(test_cache_add_nat.addE (let _,y = a0 in y) (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))
              in
              (match setCurrentBytes test_cache test_cache_add_nat sz (Pervasives.succ
                       (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))
                       (let x,_ = let x,_ = a1 in x in x) (let _,y = let x,_ = a1 in x in y)
                       (Int64Word.combine (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         0))))))))))))))))))))))))))))))) r0.stream_Identifier
                         (Pervasives.succ 0) r0.r) (let _,y = a1 in y) with
               | Some a2 ->
                 (match alignedEncodeList test_cache (fun n v0 idx1 s ce ->
                          if Nat.ltb idx1 n
                          then Some
                                 ((((fun _ ->   let rec set_nth l i x =     match l, i with     | [], 0 -> [x]     | [], _ -> 0 :: set_nth [] (i-1) x     | _ :: l, 0 -> x :: l     | y :: l, _ -> y :: set_nth l (i-1) x in   set_nth)
                                     n v0 idx1 s),(Pervasives.succ
                                 idx1)),(test_cache_add_nat.addE ce (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ 0))))))))))
                          else None) sz (let x,_ = let x,_ = a2 in x in x)
                          (let _,y = let x,_ = a2 in x in y) r0.payload (let _,y = a2 in y) with
                  | Some a3 ->
                    alignedEncode_Nil test_cache sz (let x,_ = let x,_ = a3 in x in x)
                      (let _,y = let x,_ = a3 in x in y) r0 (let _,y = a3 in y)
                  | None -> None)
               | None -> None)
         else None
    else None
  | None -> None

(** val hTTP_Frame_decoder_impl :
    OCamlNativeInt.t -> (int list) -> ((hTTP_Frame*OCamlNativeInt.t)*cacheDecode) option **)

let hTTP_Frame_decoder_impl sz v =
  match let idx = 0 in
        (match (fun _ l i -> try Some (List.nth l i) with _ -> None) sz v idx with
         | Some a ->
           Some ((a,(Pervasives.succ
             idx)),(test_cache_add_nat.addD (Obj.magic ()) (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ 0))))))))))
         | None -> None) with
  | Some a ->
    let idx = let _,y = let x,_ = a in x in y in
    (match (fun _ l i -> try Some (List.nth l i) with _ -> None) sz v idx with
     | Some a0 ->
       let a1 = (a0,(Pervasives.succ
         idx)),(test_cache_add_nat.addD (let _,y = a in y) (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ 0)))))))))
       in
       let idx0 = let _,y = let x,_ = a1 in x in y in
       (match (fun _ l i -> try Some (List.nth l i) with _ -> None) sz v idx0 with
        | Some a2 ->
          let a3 = (a2,(Pervasives.succ
            idx0)),(test_cache_add_nat.addD (let _,y = a1 in y) (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))
          in
          let a4 =
            ((Int64Word.append (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ 0))))))))
               (add (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 0)))))))) (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ 0))))))))) (let x,_ = let x,_ = a3 in x in x)
               (Int64Word.append (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ 0)))))))) (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ 0))))))))
                 (let x,_ = let x,_ = a1 in x in x) (let x,_ = let x,_ = a in x in x))),
            (let _,y = let x,_ = a3 in x in y)),(let _,y = a3 in y)
          in
          let w = let x,_ = let x,_ = a4 in x in x in
          let idx1 = let _,y = let x,_ = a4 in x in y in
          (match (fun _ l i -> try Some (List.nth l i) with _ -> None) sz v idx1 with
           | Some a5 ->
             let a6 = (a5,(Pervasives.succ
               idx1)),(test_cache_add_nat.addD (let _,y = a4 in y) (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))
             in
             let idx2 = let _,y = let x,_ = a6 in x in y in
             (match (fun _ l i -> try Some (List.nth l i) with _ -> None) sz v idx2 with
              | Some a7 ->
                let a8 = (a7,(Pervasives.succ
                  idx2)),(test_cache_add_nat.addD (let _,y = a6 in y) (Pervasives.succ
                           (Pervasives.succ (Pervasives.succ (Pervasives.succ
                           (Pervasives.succ (Pervasives.succ (Pervasives.succ
                           (Pervasives.succ 0)))))))))
                in
                let idx3 = let _,y = let x,_ = a8 in x in y in
                (match (fun _ l i -> try Some (List.nth l i) with _ -> None) sz v idx3 with
                 | Some a9 ->
                   let a10 = (a9,(Pervasives.succ
                     idx3)),(test_cache_add_nat.addD (let _,y = a8 in y) (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ 0)))))))))
                   in
                   let idx4 = let _,y = let x,_ = a10 in x in y in
                   (match (fun _ l i -> try Some (List.nth l i) with _ -> None) sz v idx4 with
                    | Some a11 ->
                      let a12 = (a11,(Pervasives.succ
                        idx4)),(test_cache_add_nat.addD (let _,y = a10 in y)
                                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ 0)))))))))
                      in
                      let idx5 = let _,y = let x,_ = a12 in x in y in
                      (match (fun _ l i -> try Some (List.nth l i) with _ -> None) sz v idx5 with
                       | Some a13 ->
                         let a14 = (a13,(Pervasives.succ
                           idx5)),(test_cache_add_nat.addD (let _,y = a12 in y)
                                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ 0)))))))))
                         in
                         let idx6 = let _,y = let x,_ = a14 in x in y in
                         (match (fun _ l i -> try Some (List.nth l i) with _ -> None) sz v
                                  idx6 with
                          | Some a15 ->
                            let a16 = (a15,(Pervasives.succ
                              idx6)),(test_cache_add_nat.addD (let _,y = a14 in y)
                                       (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ 0)))))))))
                            in
                            let a17 =
                              ((Int64Word.append (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                 0))))))))
                                 (add (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ 0))))))))
                                   (add (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ 0))))))))
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ 0))))))))))
                                 (let x,_ = let x,_ = a16 in x in x)
                                 (Int64Word.append (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                   0))))))))
                                   (add (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ 0))))))))
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ 0)))))))))
                                   (let x,_ = let x,_ = a14 in x in x)
                                   (Int64Word.append (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     0)))))))) (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     0)))))))) (let x,_ = let x,_ = a12 in x in x)
                                     (let x,_ = let x,_ = a10 in x in x)))),(let _,y =
                                                                               let x,_ = a16
                                                                               in
                                                                               x
                                                                             in
                                                                             y)),(let _,y =
                                                                                   a16
                                                                                  in
                                                                                  y)
                            in
                            let w0 = let x,_ = let x,_ = a17 in x in x in
                            (match listAlignedDecodeM test_cache sz
                                     (fun numBytes v0 idx7 c ->
                                     match (fun _ l i -> try Some (List.nth l i) with _ -> None)
                                             numBytes v0 idx7 with
                                     | Some a18 ->
                                       Some ((a18,(Pervasives.succ
                                         idx7)),(test_cache_add_nat.addD c (Pervasives.succ
                                                  (Pervasives.succ (Pervasives.succ
                                                  (Pervasives.succ (Pervasives.succ
                                                  (Pervasives.succ (Pervasives.succ
                                                  (Pervasives.succ 0))))))))))
                                     | None -> None)
                                     (Int64Word.wordToNat (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ 0)))))))))))))))))))))))) w) v
                                     (let _,y = let x,_ = a17 in x in y) (let _,y = a17 in y) with
                             | Some a18 ->
                               Some (({ length = w; type0 =
                                 (let x,_ = let x,_ = a6 in x in x); flags =
                                 (let x,_ = let x,_ = a8 in x in x); r =
                                 (id
                                   (Int64Word.split1' (Pervasives.succ 0) (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     0))))))))))))))))))))))))))))))) w0));
                                 stream_Identifier =
                                 (id
                                   (Int64Word.split2' (Pervasives.succ 0) (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                     0))))))))))))))))))))))))))))))) w0)); payload =
                                 (let x,_ = let x,_ = a18 in x in x) },(let _,y =
                                                                          let x,_ = a18 in x
                                                                        in
                                                                        y)),(let _,y = a18 in
                                                                             y))
                             | None -> None)
                          | None -> None)
                       | None -> None)
                    | None -> None)
                 | None -> None)
              | None -> None)
           | None -> None)
        | None -> None)
     | None -> None)
  | None -> None

(** val http_decode : OCamlNativeInt.t -> (int list) -> hTTP_Frame option **)

let http_decode sz =
  wrapDecoder sz hTTP_Frame_decoder_impl

(** val http_encode : OCamlNativeInt.t -> hTTP_Frame -> (int list) -> (int list) option **)

let http_encode sz =
  wrapEncoder sz hTTP_Frame_encoder_impl
