module StarCombinator.Helpers

private
let prefix = '\x1b'



let cstHEADER = "\x1b[95m"
let cstOKBLUE = "\x1b[94m"
let cstOKGREEN = "\x1b[92m"
let cstWARNING = "\x1b[93m"
let cstFAIL = "\x1b[91m"
let cstENDC = "\x1b[0m"
let cstBOLD = "\x1b[1m"
let cstUNDERLINE = "\x1b[4m"

let header str 		= cstHEADER	^ str ^ cstENDC
let okblue str 		= cstOKBLUE	^ str ^ cstENDC
let okgreen str 	= cstOKGREEN	^ str ^ cstENDC
let warning str 	= cstWARNING	^ str ^ cstENDC
let fail str 		= cstFAIL	^ str ^ cstENDC
let bold str 		= cstBOLD	^ str ^ cstENDC
let underline str 	= cstUNDERLINE	^ str ^ cstENDC
let line str            = str ^ "\n"
