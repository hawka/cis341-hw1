open Assert
open Interpreter

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)


let provided_tests : suite = [

  Test ("Student-Provided Tests for Part I", [
    ("mem addr test 001", assert_eqf (fun() -> mem_addr 0x14l) 5);
    ("mem addr test 002", (fun() -> try ignore (mem_addr 0xfffffffdl); failwith "Invalid memory address" with X86_segmentation_fault -> ()));
    ("mem addr test 003", (fun() -> try ignore (mem_addr 0x202l); failwith "Invalid memory address" with X86_segmentation_fault -> ()));
  ]);

  Test ("Student-Provided Big Test for Part II", [
  ]);
  
] 
