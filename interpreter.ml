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
let to32 = Int64.to_int32
let to64 = Int64.of_int32

exception X86_segmentation_fault of string

exception Label_value of string
exception Immediate_value of string
exception Dont_pull_that_shit of string

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
  if (addr <=@ mem_top) && (addr >=@ mem_bot) && addr_i mod 4 = 0 then
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
    | Some r -> xs.s_reg.(ind_of_reg r)
    | None   -> 0l
  and ind_scale = 
    match i.i_iscl with
    | Some (r, s) -> (xs.s_reg.(ind_of_reg r) *@ s)
    | None        -> 0l
  and disp = 
    match i.i_disp with
    | Some(DImm x) -> x
    | Some(DLbl l) -> raise (Label_value "Tried to pass a label as displacement in indirect address")
    | None         -> 0l
  in (base +@ ind_scale +@ disp)


(* Get the relevant Int32 value from a register. *)
let get_reg_val (xs:x86_state) (r:reg) : int32 =
  xs.s_reg.(ind_of_reg r)

(* Set the relevant Int32 value from a register. *)
let set_reg_val (xs:x86_state) (r:reg) (v:int32): x86_state =
  xs.s_reg.(ind_of_reg r) <- v; xs

(* Get the relevant Int32 value from an operand. *)
let get_opnd_val (xs:x86_state) (o:opnd) : int32 =
  begin match o with
  | Lbl _ -> raise (Label_value "Tried to get the value of a label")
  | Imm i -> i
  | Reg r -> get_reg_val xs r
  | Ind i -> Array.get xs.s_mem (map_addr (compute_indirect xs i))
  end


(* Set the relevant Int32 value from an operand. *)
let set_opnd_val (xs:x86_state) (o:opnd) (v:int32) : x86_state =
  begin match o with
  | Lbl _ -> raise (Label_value "Tried to set the value of a label")
  | Imm i -> raise (Immediate_value "Tried to set the value of an immediate")
  | Reg r -> set_reg_val xs r v
  | Ind i -> Array.set xs.s_mem (map_addr (compute_indirect xs i)) v; xs
  end


(* Set the condition flags by value. *)
let set_cnd_flags (xs:x86_state) (v:int32) (o:bool) : x86_state =
  xs.s_OF <- o;
  xs.s_SF <- get_bit 31 v;
  xs.s_ZF <- v = Int32.zero;
  xs


(* Apply a binary Int32 opearation from a source to destination registers. *)
let apply_op (op:int32 -> int32 -> int32) (s:opnd) (d:opnd) (n_OF:bool) (xs:x86_state) =
  let v = op (get_opnd_val xs d) (get_opnd_val xs s) in
  let xs' = set_cnd_flags xs v n_OF in
  set_opnd_val xs' d v 


(* Apply an Int32 shift opearation from a source to destination registers. *)
let apply_shift (op:int32 -> int -> int32) (d:opnd) (amt:opnd) (xs:x86_state) (is_arith:bool) =
  let int_amt = (Int32.to_int (get_opnd_val xs amt)) 
  and dest = (get_opnd_val xs d) in
  let v = (op dest int_amt) in
  let n_OF = (if is_arith then (if int_amt = 1 then false else xs.s_OF)
                else if ((int_amt = 1) && (get_bit 31 dest <> get_bit 30 dest))
                     then (get_bit 31 dest) 
                else xs.s_OF) in
  let xs' = (if (int_amt <> 0) then (set_cnd_flags xs v n_OF) else xs) in
  set_opnd_val xs' d v


(* Get the 64-bit sign-extensions of two register. *)
let int64_of_opnd (xs:x86_state) (o:opnd) : int64 = 
  to64 (get_opnd_val xs o)

(* Get the 32-bit truncation of a 64-bit op. *)
let int32_of_op (op:int64 -> int64 -> int64) (x:int64) (y:int64) : int32 =
  to32 (op x y)

(* Return if a 64-bit integer is negative. *)
let is_neg (x:int64) : bool = Int64.compare x (Int64.zero) < 0

(* xor *)
let xor (b1:bool) (b2:bool) : bool =
  (b1 && not b2) || (b2 && not b1)

(* subtract *)
let do_subtract (set_regs:bool) (xs:x86_state) (d:opnd) (s:opnd) : x86_state =
  let d64 = int64_of_opnd xs d in
  let s64 = int64_of_opnd xs s in
  let r32 = int32_of_op Int64.sub d64 s64 in
  let o_flag =
    (Int32.min_int = to32 s64) ||
      ((xor (is_neg s64) (is_neg d64)) &&
          not (xor (is_neg s64) (r32 <@ 0l))) in
  let xs' = if set_regs then set_opnd_val xs d r32 else xs in
  set_cnd_flags xs' r32 o_flag

(* Get the label form an operand or throw an error. *)
let get_lbl (o:opnd) : lbl =
  begin match o with
  | Lbl l -> l
  | _     -> raise (Dont_pull_that_shit "Only labels are allowed here")
  end
  

let rec interpret_insn (xs:x86_state) (lbl_map:insn_block LblMap.t)
    (i:insn) : x86_state =
  begin match i with
  (* arithmetic *)
  | Neg(d)     -> let v = Int32.neg (get_opnd_val xs d) in
                  let xs' = set_cnd_flags xs v (Int32.min_int = v) in
                  set_opnd_val xs' d v
  | Add(d, s)  -> let d64 = int64_of_opnd xs d in
                  let s64 = int64_of_opnd xs s in
                  let r32 = int32_of_op Int64.add d64 s64 in
                  let o_flag =
                    not (xor (is_neg s64) (is_neg d64)) &&
                      (xor (is_neg s64) (r32 <@ 0l)) in
                  let xs' = set_cnd_flags xs r32 o_flag in
                  set_opnd_val xs' d r32
  | Sub(d, s)  -> do_subtract true xs d s
  | Imul(d, s) -> let d64 = to64 (get_reg_val xs d) in
                  let s64 = int64_of_opnd xs s in
                  let r64 = Int64.mul d64 s64 in
                  let r32 = to32 r64 in
                  let o_flag = to64 r32 <> r64 in
                  let xs' = set_cnd_flags xs r32 o_flag in
                  set_reg_val xs' d r32

  (* logic *)
  | Not(d)    -> set_opnd_val xs d (Int32.lognot (get_opnd_val xs d))
  | And(d, s) -> apply_op Int32.logand s d false xs
  | Or(d, s)  -> apply_op Int32.logor s d false xs
  | Xor(d, s) -> apply_op Int32.logxor s d false xs

  (* bitmanip *)
  | Sar(d, amt) -> apply_shift Int32.shift_right d amt xs true
  | Shl(d, amt) -> apply_shift Int32.shift_left d amt xs false
  | Shr(d, amt) -> apply_shift Int32.shift_right_logical d amt xs false
  | Setb(d, cc) -> if (condition_matches xs cc) 
                     then (set_opnd_val xs d (Int32.logor (get_opnd_val xs d) 1l))
                   else if ((get_bit 0 (get_opnd_val xs d)))
                     then (set_opnd_val xs d (Int32.logxor (get_opnd_val xs d) 1l))
                   else xs 

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
                     let  xs' = set_opnd_val xs (Reg Esp) new_esp in
                     set_opnd_val xs' d v

  (* controlflow & conds *)
  | Cmp(s1, s2) -> do_subtract false xs s1 s2
  | Jmp(s)      -> interpret_block xs lbl_map (get_lbl s)
  | Call(s)     -> let new_esp = (get_opnd_val xs (Reg Esp)) -@ 4l in
                   let xs' = set_opnd_val xs (Reg Esp) new_esp in
                   interpret_block xs' lbl_map (get_lbl s)
  | Ret         -> set_opnd_val xs (Reg Esp) ((get_opnd_val xs (Reg Esp)) +@ 4l)
  | J(cc, clbl) ->
    if condition_matches xs cc then interpret_block xs lbl_map clbl else xs
  end

and interpret_insns (xs:x86_state) (lbl_map:insn_block LblMap.t)
    (insns:insn list) : x86_state = 
  begin match insns with
  | []  -> raise (Dont_pull_that_shit "Y u no have code: code block can't be empty")
  | [h] ->
    begin match h with
    | Jmp(s)  -> interpret_insn xs lbl_map h
    | Ret     -> interpret_insn xs lbl_map h
    | J(c, l) -> interpret_insn xs lbl_map h
    | _       ->
      raise (Dont_pull_that_shit "Code block must end with Jmp, Ret, or J")
    end
  | h::t ->
    begin match h with
    | Jmp(_)  -> interpret_insn xs lbl_map h
    | J(c, _) ->
      if condition_matches xs c then
        interpret_insn xs lbl_map h
      else
        interpret_insns (interpret_insn xs lbl_map h) lbl_map t
    | _       -> interpret_insns (interpret_insn xs lbl_map h) lbl_map t
    end
  end

and interpret_block (xs:x86_state) (lbl_map:insn_block LblMap.t)
    (l:lbl) : x86_state =
  let next_block = LblMap.find l lbl_map in 
    interpret_insns xs lbl_map next_block.insns



let interpret (code:insn_block list) (xs:x86_state) (l:lbl) : unit =
  let lbl_map = mk_lbl_map code in
    interpret_block xs lbl_map l; ()

      
let run (code:insn_block list) : int32 =
  let main = X86.mk_lbl_named "main" in
  let xs = mk_init_state () in
  let _ = interpret code xs main in
    xs.s_reg.(eaxi)
      
