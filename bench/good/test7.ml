
external x : int ref

let test7 = begin x := (!x + 1) { result = x+1 }; 
                  x := (!x + 2) { result = x+2 } end { x > x@ }



