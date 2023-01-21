open Core

let yojson_of_hashtbl yojson_of_key yojson_of_data tbl =
  `List
    (Hashtbl.fold tbl ~init:[] ~f:(fun ~key ~data acc ->
         `List [yojson_of_key key; yojson_of_data data] :: acc ) )

let hashtbl_of_yojson modl key_of_yojson data_of_yojson = function
  | `List l ->
      let tbl = Hashtbl.create modl in
      List.iter l ~f:(function
        | `List [yojson_key; yojson_data] ->
            Hashtbl.add_exn tbl ~key:(key_of_yojson yojson_key)
              ~data:(data_of_yojson yojson_data)
        | _ ->
            failwith "hashtbl_of_yojson: length-two list needed" ) ;
      tbl
  | _ ->
      failwith "hashtbl_of_yojson: list needed"

let yojson_of_map yojson_of_key yojson_of_data map =
  `List
    (Map.fold map ~init:[] ~f:(fun ~key ~data acc ->
         `List [yojson_of_key key; yojson_of_data data] :: acc ) )

let map_of_yojson modl key_of_yojson data_of_yojson = function
  | `List l ->
      List.fold l ~init:(Map.empty modl) ~f:(fun map -> function
        | `List [yojson_key; yojson_data] ->
            Map.add_exn map ~key:(key_of_yojson yojson_key)
              ~data:(data_of_yojson yojson_data)
        | _ ->
            failwith "map_of_yojson: length-two list needed" )
  | _ ->
      failwith "map_of_yojson: list needed"

let sub name' value' = function
  | `Assoc attrs ->
      `Assoc
        (List.map attrs ~f:(fun (name, value) ->
             if String.(name = name') then (name, value') else (name, value) )
        )
  | _ ->
      failwith "can only sub keys of JSON object"
