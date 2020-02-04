loadf (complete_nuprl_path ``lib 2-0-tactics`` `load`) ;; 

loadf `reflection`;;

map (\ name. execute_command_line (`load bot from ` 
                                   ^ complete_nuprl_path ``lib meta`` name))
    ``init basic list set rec tenv env pbool 
      typechecking subenv meta1 meta2 meta3 meta4 q``
;;

