set_display_maintenance_mode false;;
make_all_tags_legal false;;
map (\ name. execute_command_line (`load fully bot from ` 
                                   ^ complete_nuprl_path ``libraries meta`` name))
    ``init basic list set rec tenv env pbool 
      typechecking subenv``
;;

