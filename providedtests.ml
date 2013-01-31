open Assert
open Interpreter

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)


let provided_tests : suite = [
  Test("Student-Provided Tests for Part I", [
    ("map addr test 001", assert_eqf (fun() -> map_addr 0xfffff014l) 5);
    ("map addr test 002", (fun() ->
			try ignore (map_addr 0xfffffffdl);
					failwith "Invalid memory address" with X86_segmentation_fault _ -> ()));
    ("map addr test 003", (fun() ->
			try ignore (map_addr 0x00000202l);
					failwith "Invalid memory address" with X86_segmentation_fault _ -> ()));
  ]);
(*
  Test("Student-Provided Big Test for Part II", [("gcd(15,20)", run_test 5l
    [
      (mk_insn_block (mk_lbl_named "main") [
        Push (Imm 15l); (* a *)
        Push (Imm 20l); (* b *)
        Mov (eax, stack_offset 8l); (* eax = a *)
        Cmp (eax, Imm 0l);          (* if a = 0 *)
        J (NotEq, mk_lbl_named "gcd_loop")
        
    ]
  ]);  
*)
] 
