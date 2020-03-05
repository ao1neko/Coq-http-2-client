Require Import
        Coq.Strings.String
        Coq.Vectors.Vector
        Coq.omega.Omega.

Require Import
        Fiat.Common.SumType
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Computation
        Fiat.Narcissus.BinLib
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeCheckSum
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats
        Fiat.Narcissus.Formats.Vector
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Automation.AlignedAutomation.

Require Import Bedrock.Word.

Import Vectors.Vector.VectorNotations.
Open Scope string_scope.

(* 疑問　
Compose_Formatの返り値 FormatM S T　ではないと
%とは
++ sequence_format
padding
*)


Check word.
Check WO~0~1.
Check WS true WO~0~0.
Check Comp. (*(xxy)*)
Print Cache.
Print CacheAdd. (* addEを見て *)
Print Monoid. (* 二項演算,単位元*)
Print QueueMonoidOpt. (* T bool *)  
Print encode_word'. (* format_word = (encode_word' nat word8 e ,addE CacheFormat nat)*)
Check addE. (* indexを+ *)



Print format_SumType.
Check ilist. (* vector からvector への写像　*)
Print SumType. (*vectorを1つずつ要素をTに変換する　返り値は:T:Type*)
Check SumType_index.
Print Fin.t .
Check SumType_proj.
Check ith.

(* Our source data type for IP packets. *)
Record HTTP_Frame :=
  { Length : word 24;
    type : word 8; (* frame type*)
    Flags : word 8;
    R : word 1;
    Stream_Identifier : word 31; 
    payload : list (word 8) }.


Check Length.
Print Projection_Format. (* 点記号*)
Print Compose_Format. (* 引数: format_word , Prop.. Length HTTPFrame = word 24  返り値:f *)
Print computes_to. (* 元かどうかProp *)


Record name1 :=
  {data1: word 8 }.
Record name2 :=
  {data2: word 8 }.

Definition RecordTypes :=
  [   name1;
      name2
  ].

Definition format1  :=
  format_word ◦ data1.

Definition format2 :=
  format_word ◦ data2.
  
(* S=HTTP_Frmae T=ByteString としたFormatM *)
Definition HTTP_Frame_Format :=
  (format_word  ◦ Length
               ++ format_word ◦ type
               ++ format_word ◦ Flags
               ++ format_word ◦ R
               ++ format_word ◦ Stream_Identifier
               ++ format_list format_word ◦ payload)%format.




Definition HTTP_Frame_OK (http : HTTP_Frame) :=
   (| (http.(payload))|) = wordToNat http.(Length).
  
Print CorrectAlignedEncoderFor. (* encode: AlignedEncodeM sz *)
Print AlignedEncodeM. (* bytebuffer:n個の文字列 , nat:index,.. *)
Print  CorrectAlignedEncoder. (*encoderとformat合成*)
(* format s env を満たす (T*chace) > encoder' の返り値 (T*Chace )*)
(* env =状態, benv = (T*Cache) *)
Print refine. (* new は old の部分集合 = True*)
Print Return.
Print padding.

Print EncodeMEquivAlignedEncodeM. (* EncodeM , AlignedEncodeM これ以降はまだ*)



(* つまりEncoderM *)
Definition HTTP_Frame_encoder :
  CorrectAlignedEncoderFor HTTP_Frame_Format.
Proof.
  synthesize_aligned_encoder.
Defined.


(*bite数,vector, HTTP_Frame *)
Definition HTTP_Frame_encoder_impl {sz} v r :=
  Eval simpl in (projT1 HTTP_Frame_encoder sz v 0 r tt).

Print HTTP_Frame_encoder_impl.

Definition HTTP_Frame_decoder :
  CorrectAlignedDecoderFor HTTP_Frame_OK HTTP_Frame_Format.
Proof.
  synthesize_aligned_decoder.
Defined.

Print CorrectAlignedDecoderFor.

Arguments GetCurrentBytes : simpl never.
Definition HTTP_Frame_decoder_impl {sz} v :=
  Eval simpl in (projT1 HTTP_Frame_decoder sz v 0 ()).



  Local Transparent weqb.
  Local Transparent natToWord.

(* An source version of a packet, different from binary packet above. *)
Definition pkt :=
  {| Length := natToWord 24 10;
     type := natToWord 8 8;
     Flags := natToWord 8 8;
     R:= natToWord 1 0;
     Stream_Identifier := natToWord 31 8;
     payload := List.map (natToWord 8) [1;1;1;1;0;0;0;0]
  |}.

Local Transparent natToWord.
Local Transparent weqb.
(* This should succeed, *)
Definition test1 :=
    Ifopt (HTTP_Frame_encoder_impl (initialize_Aligned_ByteString 100) pkt)
  as bs Then HTTP_Frame_decoder_impl (fst (fst bs))
        Else None.

Require Import Fiat.Narcissus.Examples.NetworkStack.TestInfrastructure.



Definition http_decode {sz} :=
  WrapDecoder sz (@HTTP_Frame_decoder_impl).


Definition http_encode {sz} :=
  WrapEncoder sz (@HTTP_Frame_encoder_impl).

Check http_encode. 

Require Import
        Narcissus.OCamlExtraction.Extraction.
    

Extract Inductive Vector.t =>
"StackVector.t"
  ["StackVector.empty()" "StackVector.cons"]
  "StackVector.destruct".
Extract Inductive VectorDef.t =>
"StackVector.t"
  ["StackVector.empty()" "StackVector.cons"]
  "StackVector.destruct".

Extract Inlined Constant Vector.nth => "StackVector.nth".
Extract Inlined Constant VectorDef.nth => "StackVector.nth".
Extract Inlined Constant Vector_nth_opt => "StackVector.nth_opt".
Extract Inlined Constant EnumOpt.word_indexed => "StackVector.index".



Require Import Fiat.Narcissus.BinLib.AlignedByteString.
Require Import Fiat.Narcissus.BinLib.AlignedByteBuffer.
Extract Inlined Constant ByteBuffer.t => "(int list)".
Extract Inlined Constant ByteBuffer.nil => "[]".
Extract Inlined Constant ByteBuffer.cons => "(fun (hd, _, tl) -> hd :: tl)".
Extract Inlined Constant ByteBuffer.hd => "(fun _ (hd :: _) -> hd)".
Extract Inlined Constant ByteBuffer.tl => "(fun _ (_ :: tl) -> tl)".
Extract Inlined Constant ByteBuffer.to_list => "(fun l -> l)".
Extract Inlined Constant ByteBuffer.of_list => "(fun l -> l)".

Extract Inlined Constant ByteBuffer.append => "(fun _ _ -> ( @ ))".
Extract Inlined Constant ByteBuffer.drop =>
"(fun n _ -> 
  let rec drop n xs =
    if n <= 0
    then xs
    else match xs with [] -> [] | _ :: xs -> drop (n-1) xs in 
  drop n)".
Extract Inlined Constant nth_opt => "(fun _ l i -> try Some (List.nth l i) with _ -> None)".
Extract Inlined Constant set_nth' =>
"(fun _ ->
  let rec set_nth l i x =
    match l, i with
    | [], 0 -> [x]
    | [], _ -> 0 :: set_nth [] (i-1) x
    | _ :: l, 0 -> x :: l
    | y :: l, _ -> y :: set_nth l (i-1) x in
  set_nth)".
Extract Inlined Constant initialize_Aligned_ByteString => "(fun _ -> [])". 
Extraction "http2en.ml" http_decode http_encode.

