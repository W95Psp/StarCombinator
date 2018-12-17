exception EOF
type mi_fd_read = in_channel
type mi_fd_write = out_channel
let pr  = Printf.printf
let spr = Printf.sprintf
let fpr = Printf.fprintf

let mi_print_newline = print_newline
let mi_print_string s = pr "%s" s; flush stdout
let mi_print_uint8 s = pr "%.02x" s; flush stdout
let mi_print_uint8_dec s = print_int s; flush stdout

let mi_print_uint32 s = pr "%.04x" s; flush stdout
let mi_print_uint32_dec s = print_int s; flush stdout
let mi_print_uint64 s = pr "%.08x" s; flush stdout
let mi_print_uint64_dec s = print_int s; flush stdout
let mi_print_any s = output_value stdout s; flush stdout
let mi_input_line = read_line
let mi_input_int () = Z.of_int (read_int ())
let mi_input_float = read_float
let mi_open_read_file = open_in
let mi_open_write_file = open_out
let mi_close_read_file = close_in
let mi_close_write_file = close_out
let mi_read_line fd = try Pervasives.input_line fd with End_of_file -> raise EOF
let mi_write_string = output_string

let mi_readdir path = Array.to_list (Sys.readdir path)
let mi_file_exists = Sys.file_exists

let mi_fail s = print_string s; exit 0; false
                   
let mi_debug_print_string s = print_string s; false
