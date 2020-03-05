open Http;;
open Http2;;
open Int64Word;;


let ()=
  print_endline "start";
  
  let setting_frame:Http.hTTP_Frame ={length=0x000000;
             type0=0x04;
             flags=0x00;
             r=0x00;
             stream_Identifier=0x000000;
             payload=[]} in
  let header_frame:Http.hTTP_Frame={length=0x00000b;
                    type0=0x01;
                    flags=0x05;
                    r=0x00;
                    stream_Identifier=0x000033;
                    payload=[0x82;0x87;0x84;0x66;0x86;0xa0;0xe4;0x1d;0x13;0x9d;0x09]} in
  let connection_preface = [0x50;0x52;0x49;0x20;0x2a;0x20;0x48;0x54;0x54;0x50;
                            0x2f;0x32;0x2e;0x30;0x0d;0x0a;0x0d;0x0a;0x53;0x4d;
                            0x0d;0x0a;0x0d;0x0a] in

  let func1 = http_encode(100) in
  let func2 =func1(setting_frame) in
  let func3=http_encode(100) in
  let func4=func3(header_frame) in
  let setting_optionlist=func2([]) in
  let header_optionlist =func4([]) in
  
  match setting_optionlist with
  | None -> print_endline "error at encoder";
  | Some ilist ->
     
  match header_optionlist with
  | None -> print_endline "error at encoder2";
  | Some ilist2 ->
     
  print_endline "setting_frame";
  List.iter (Printf.printf "0x%x ") ilist;
  print_string "\n";
  
  print_endline "\nheader_frame";
  List.iter (Printf.printf "0x%x ") ilist2;
  print_string "\n";

  
  let cmd = "openssl s_client -quiet -state -connect localhost:443" in
  let inchan,outchan = Unix.open_process cmd in

  try        
    List.iter (output_byte outchan) connection_preface;
    List.iter (output_byte outchan) ilist ;
    List.iter (output_byte outchan) ilist2 ;  
    
    let _ = flush outchan in
    let count = 0 in
    let mylist = ref [] in
    


    print_endline "decode start";
    
    let rec loop () =   
    match http_decode2 0 (Buffer.create 256,inchan) with
    | Some frame ->
       Printf.printf "length:%d\n" frame.length ;
       Printf.printf "type:%d\n" frame.type0 ;
       Printf.printf "flag:%d\n" frame.flags ;
       Printf.printf "R:%d\n" frame.r ;
       Printf.printf "stream_Identifier:%d\n" frame.stream_Identifier ;
       begin match frame.type0 with
       | 0x00 -> List.iter (fun c -> print_char (Char.chr c)) frame.payload;flush stdout;loop() 
       | 0x07 ->()
       | _ -> loop()            
       end   
    | None -> ()
    in
    
    loop();
    flush stdout;
    (*        
    let rec loop () =
      match input_char inchan with
      |'!'->()
      | c -> Printf.printf "%c" c ; loop ()
      | exception End_of_file -> ()
    in
    loop ();
     *)
              
    ignore(Unix.close_process_in inchan);
    print_endline "finish"; 
    
  with e->
    prerr_endline (raise e);
    ignore (Unix.close_process_in inchan);
;;
