open Assert
open Interpreter

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)


let provided_tests : suite = [

  Test ("Student-Provided Tests for Part I", [
    ("map addr test 001", assert_eqf (fun() -> map_addr 0xfffff014l) 5);
    ("map addr test 002", (fun() -> try ignore (map_addr 0xfffffffdl); failwith "Invalid memory address" with X86_segmentation_fault _ -> ()));
    ("map addr test 003", (fun() -> try ignore (map_addr 0x00000202l); failwith "Invalid memory address" with X86_segmentation_fault _ -> ()));
  ]);

  Test ("Student-Provided Big Test for Part II", [
  ]);
  
] 
