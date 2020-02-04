%-*- Default-character-style: (:FIX :ROMAN :VERY-LARGE) -*-%

let write_theorem name =
  let p = proof_of_theorem name in
  open_snapshot_file (); 
  print_return (); 
  print_return ();
  print_return (); 
  print_return ();
  print name;
  print ` (`; 
  print (tok_of_int (nodes p));
  print `):`;
  print_return (); 
  print_return (); 
  print_proof 0 [] p;
  close_snapshot_file ()
;;

% Ignore def extractions %
let theorems_in_library () =
  filter (\x. object_kind x = `THM` & remove_trailing_underscores x = x ? false)
         (library())
;;