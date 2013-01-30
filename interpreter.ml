(* CIS341: Project 1 Interpreter *)
(* Author: Steve Zdancewic *)

open X86

(* Int32 / Int64 abbreviations and infix arithmetic *)
let (+@) = Int32.add
let (-@) = Int32.sub
let (/@) = Int32.div
let ( *@ ) = Int32.mul
let (<@) a b = (Int32.compare a b) < 0
let (<=@) a b = (Int32.compare a b) <= 0
let (>@) a b = (Int32.compare a b) > 0
let (>=@) a b = (Int32.compare a b) >= 0
let (<@@) a b = (Int64.compare a b) < 0

exception X86_segmentation_fault of string

exception Label_value of string
exception Immediate_value of string

(* Interpret the registers as indices into the register file array *)
let eaxi = 0
let ebxi = 1
let ecxi = 2
let edxi = 3
let esii = 4
let edii = 5
let ebpi = 6
let espi = 7 

let get_register_id = function
  | Eax -> eaxi 
  | Ebx -> ebxi 
  | Ecx -> ecxi 
  | Edx -> edxi 
  | Esi -> esii 
  | Edi -> edii 
  | Ebp -> ebpi
  | Esp -> espi


let mem_size = 1024                 (* Size of memory in words *)
let mem_top : int32 = 0xfffffffcl   (* Last addressable memory location *)
let mem_bot : int32 =               (* First addressable memory location *)
    (Int32.of_int (mem_size * 4)) *@ (-1l)

(* 
   Maps virtual addresses (int32 addresses) to physical addresses (int indices). 
   Raises an X86_segmentation_fault exception if the provided virtual address 
   does not map or if the address is unaligned. 
*)
let map_addr (addr:int32) : int =
  let addr_i : int = Int32.to_int (addr -@ 0xfffff000l) in
  if (addr <=@ mem_top) && (addr >=@ (mem_top +@ mem_bot)) && addr_i mod 4 = 0 then
    (addr_i / 4)
  else
    raise (X86_segmentation_fault "Invalid memory address")

type x86_state = {
    s_mem : int32 array;    (* 1024 32-bit words -- the heap *)
    s_reg : int32 array;    (* 8 32-bit words -- the register file *)
    mutable s_OF : bool;    (* overflow flag *)
    mutable s_SF : bool;    (* sign bit flag *)
    mutable s_ZF : bool;    (* zero flag *)
}

let mk_init_state () : x86_state = 
  let xs = {
  s_mem = Array.make mem_size 0l;
  s_reg = Array.make 8 0l;
  s_OF  = false;
  s_SF  = false;
  s_ZF  = false;
  } in
  xs.s_reg.(espi) <- mem_top; xs 

let print_state (xs:x86_state) : unit =
  (Array.iter (fun e -> Printf.printf "%lx " e) xs.s_mem);
  (Printf.printf "\neax: %lx ebx: %lx ecx: %lx edx: %lx" xs.s_reg.(eaxi)
      xs.s_reg.(ebxi) xs.s_reg.(ecxi) xs.s_reg.(edxi));
  (Printf.printf "\nesi: %lx edi: %lx ebp: %lx esp: %lx" xs.s_reg.(esii)
      xs.s_reg.(edii) xs.s_reg.(ebpi) xs.s_reg.(espi));
  (Printf.printf "\nOF: %b SF: %b ZF: %b\n" xs.s_OF xs.s_SF xs.s_ZF)
  

(* Helper function that determines whether a given condition code
   applies in the x86 state xs. *)  
let condition_matches (xs:x86_state) (c:X86.cnd) : bool =
  begin match c with 
  | Sgt -> not (xs.s_SF <> xs.s_OF || xs.s_ZF)
  | Sge -> (xs.s_SF = xs.s_OF)
  | Slt -> (xs.s_SF <> xs.s_OF)
  | Sle -> (xs.s_SF <> xs.s_OF || xs.s_ZF)
  | Eq -> xs.s_ZF
  | NotEq -> not xs.s_ZF
  | Zero -> xs.s_ZF
  | NotZero -> not xs.s_ZF
  end


(* Returns the bit at a given index in a 32-bit word as a boolean *)
let get_bit bitidx n =
  let shb = Int32.shift_left 1l bitidx in
  Int32.logand shb n = shb  


module LblMap = Map.Make(struct type t = lbl let compare = compare end)

(* Make a label. *)
let rec mk_lbl_map (code:insn_block list) : insn_block LblMap.t =
  begin match code with
  | []   -> LblMap.empty
  | h::t -> LblMap.add (h.label) h (mk_lbl_map t)
  end


(* The index of a register. *)
let ind_of_reg (r:reg) : int =
  begin match r with
  | Eax -> 0 | Ebx -> 1 | Ecx -> 2 | Edx -> 3
  | Esi -> 4 | Edi -> 5 | Ebp -> 6 | Esp -> 7
  end


let compute_indirect (xs:x86_state) (i:ind) : int32 =
  let base = 
    match i.i_base with
    | Some r -> (Array.get xs.s_reg (ind_of_reg r))
    | None   -> 0l
  and ind_scale = 
    match i.i_iscl with
    | Some (r, s) -> ((Array.get xs.s_reg (ind_of_reg r)) *@ s)
    | None        -> 0l
  and disp = 
    match i.i_disp with
    | Some(DImm x) -> x
    | Some(DLbl l) -> raise (Label_value "Tried to pass a label as displacement in indirect address")
    | None         -> 0l
  in (base +@ ind_scale +@ disp)


(* Get the relevant Int32 value from an operand. *)
let get_opnd_val (xs:x86_state) (o:opnd) : int32 =
  begin match o with
  | Lbl _ -> raise (Label_value "Tried to get the value of a label")
  | Imm i -> i
  | Reg r -> Array.get xs.s_reg (ind_of_reg r)
  | Ind i -> Array.get xs.s_mem (map_addr (compute_indirect xs i))
  end


(* Set the relevant Int32 value from an operand. *)
let set_opnd_val (xs:x86_state) (o:opnd) (v:int32) : x86_state =
  begin match o with
  | Lbl _ -> raise (Label_value "Tried to set the value of a label")
  | Imm i -> raise (Immediate_value "Tried to set the value of an immediate")
  | Reg r -> Array.set xs.s_reg (ind_of_reg r) v; xs
  | Ind i -> Array.set xs.s_mem (map_addr (compute_indirect xs i)) v; xs
  end


(* Set the condition flags by value. *)
let set_cnd_flags (xs:x86_state) (v:int32) (o:bool) : x86_state =
  xs.s_OF <- o;
  xs.s_SF <- get_bit 31 v;
  xs.s_ZF <- v = Int32.zero;
  xs


(* Apply a binary Int32 opearation from a source to destination registers. *)
let apply_op (op:int32 -> int32 -> int32) (s:opnd) (d:opnd) (xs:x86_state) =
	let v = op (get_opnd_val xs d) (get_opnd_val xs s) in
	set_opnd_val (* (set_flags_by_val xs v false) *) xs d v 


(* Apply an Int32 shift opearation from a source to destination registers. *)
let apply_shift (op:int32 -> int -> int32) (d:opnd) (amt:opnd) (xs:x86_state) =
	set_opnd_val xs d (op (get_opnd_val xs d) (Int32.to_int (get_opnd_val xs amt)))


(* TODO deal with setting condition codes? *)
let interpret_insn (xs:x86_state) (i:insn) : x86_state =
  begin match i with
  (* arithmetic *)
  | Neg(d)     -> set_opnd_val xs d (Int32.neg (get_opnd_val xs d))
  | Add(d, s)  -> xs (* TODO *)
  | Sub(d, s)  -> xs (* TODO *)
  | Imul(d, s) -> (* d1 must be a register *) (* "TODO" *) xs
  (* logic *)
  | Not(d)    -> set_opnd_val xs d (Int32.lognot (get_opnd_val xs d))
  | And(d, s) -> apply_op Int32.logand s d xs
  | Or(d, s)  -> apply_op Int32.logor s d xs
  | Xor(d, s) -> apply_op Int32.logxor s d xs
  (* bitmanip *)
  | Sar(d, amt) -> apply_shift Int32.shift_right d amt xs
  | Shl(d, amt) -> apply_shift Int32.shift_left d amt xs
  | Shr(d, amt) -> apply_shift Int32.shift_right_logical d amt xs
  | Setb(d, cc) -> if (condition_matches xs cc) 
                      then (apply_op Int32.logor d (Imm 1l) xs) 
                   else if ((get_bit 31 (get_opnd_val xs d)))
                           then (apply_op Int32.logxor d (Imm 1l) xs)
                        else xs (* TODO - put apply_op so condition codes are set? *)
  (* datamove *) 
  | Lea(d, ind) -> let addr = (compute_indirect xs ind) in
                    (set_opnd_val xs (Reg d) addr)
  | Mov(d, s)   -> set_opnd_val xs d (get_opnd_val xs s)
  | Push(s)     -> let new_esp = ((get_opnd_val xs (Reg Esp)) -@ 4l) 
                   and v = (get_opnd_val xs s) in
                     Array.set xs.s_mem (map_addr new_esp) v;
                     set_opnd_val xs (Reg Esp) new_esp
  | Pop(d)      -> let old_esp = (get_opnd_val xs (Reg Esp)) in
                     let new_esp = (old_esp +@ 4l)
                     and v = (Array.get xs.s_mem (map_addr old_esp)) in
                       set_opnd_val xs (Reg Esp) new_esp;
                       set_opnd_val xs d v
  (* controlflow & conds *)
  | Cmp(s1, s2) -> xs (* TODO *)
  | Jmp(s)      -> xs (* TODO *)
  | Call(s)     -> xs (* TODO *)
  | Ret         -> xs (* TODO *) 
  | J(cc, clbl) -> xs (* TODO *)
  end


let rec find_lbl (lbl_map:insn_block LblMap.t) (l:lbl) : unit =
  (* find the mapped insn_block.insn_list for lbl l in lbl_map *)
  (* run helper function to deal with contents of insn_block and give us 
  the last insn which should be jump or ret. if not, EXCEPTION *)
  (* parse that.. if ret, ret up. if jmp, call find_lbl lbl_map newlabel *)
	failwith "TODO"

let interpret (code:insn_block list) (xs:x86_state) (l:lbl) : unit =
(*  let lbl_map = mk_lbl_map code in*)
	failwith "TODO"
  

      
let run (code:insn_block list) : int32 =
  let main = X86.mk_lbl_named "main" in
  let xs = mk_init_state () in
  let _ = interpret code xs main in
    xs.s_reg.(eaxi)
      
