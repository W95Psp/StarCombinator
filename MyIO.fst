module MyIO

open FStar.All

exception EOF
assume new type mi_fd_read : Type0
assume new type mi_fd_write : Type0

assume val mi_print_newline : unit -> ML unit
assume val mi_print_string : string -> ML unit
assume val mi_print_uint8 : FStar.UInt8.t -> ML unit
assume val mi_print_uint8_dec : FStar.UInt8.t -> ML unit
assume val mi_print_uint32 : FStar.UInt32.t -> ML unit
assume val mi_print_uint32_dec : FStar.UInt32.t -> ML unit
assume val mi_print_uint64 : FStar.UInt64.t -> ML unit
assume val mi_print_uint64_dec : FStar.UInt64.t -> ML unit
assume val mi_print_any : 'a -> ML unit
assume val mi_input_line : unit -> ML string
assume val mi_input_int : unit -> ML int
assume val mi_input_float : unit -> ML FStar.Float.float
assume val mi_open_read_file : string -> ML mi_fd_read
assume val mi_open_write_file : string -> ML mi_fd_write
assume val mi_close_read_file : mi_fd_read -> ML unit
assume val mi_close_write_file : mi_fd_write -> ML unit
assume val mi_read_line : mi_fd_read -> ML string
assume val mi_write_string : mi_fd_write -> string -> ML unit

assume val mi_readdir : string -> ML (list string)
assume val mi_file_exists : string -> ML bool

assume val mi_fail: string -> Tot bool

(* assume val *) 

(*
   An UNSOUND escape hatch for printf-debugging;
   Although it always returns false, we mark it
   as returning a bool, so that extraction doesn't
   erase this call.
   Note: no guarantees are provided regarding the order
   of eassume valuation of this function; since it is marked as pure,
   the compiler may re-order or replicate it.
*)
assume val mi_debug_print_string : string -> Tot bool
