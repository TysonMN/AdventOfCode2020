module Day20Tyson

open System.Text.RegularExpressions

type Color = Black | White

type Transform = Flip | Rotate

type TileId = int
type TileBody = Color seq seq
type Tile = {
  Id: TileId
  Body: TileBody
}

type BorderHash = int16
type Border = {
  TileId: TileId
  Hash: BorderHash
}


let flip f b a = f a b

let map get set f a =
  a |> get |> f |> flip set a


[<Struct>]
type OptionalBuilder =
  member _.Bind(ma, f) =
    ma |> Option.bind f
  member _.Return(a) =
    Some a
  member _.ReturnFrom(ma) =
    ma
    
let option = OptionalBuilder()


module Kvp =

  open System.Collections.Generic

  let key (kvp: KeyValuePair<_,_>) =
    kvp.Key

  let value (kvp: KeyValuePair<_,_>) =
    kvp.Value


module Func2 =

  let curry f a b = f (a, b)
  let uncurry f (a, b) = f a b


module Pair =

  let ofSingle a = a, a

  let biMap f g (a, b) = (f a, g b)
  let mapAll f = biMap f f
  
  let map1 f = biMap f id
  let map2 f = biMap id f


module SeqPair =

  let map1 f = f |> Pair.map1 |> Seq.map
  let map2 f = f |> Pair.map2 |> Seq.map
  
  let filter1 f = fst >> f |> Seq.filter
  let filter2 f = snd >> f |> Seq.filter
  
  let fst mma = mma |> Seq.map fst
  let snd mma = mma |> Seq.map snd

  let scan1 f (c: 'c) (mmab: ('a * 'b) seq) =
    Seq.zip
      (mmab |> fst |> Seq.scan f c |> Seq.skip 1)
      (mmab |> snd)

  let scan2 f (c: 'c) (mmab: ('a * 'b) seq) =
    Seq.zip
      (mmab |> fst)
      (mmab |> snd |> Seq.scan f c |> Seq.skip 1)


module Transform =

  let reduce body =
    body
    |> Seq.map (function
      | Rotate -> Seq.rev << Seq.transpose // rotate counterclockwise
      | Flip   -> Seq.rev)                 // flip around vertical axis
    |> Seq.fold (>>) id


module Border =

  let private toBit = function Black -> 1s | White -> 0s

  let toHash source : BorderHash =
    let f = Seq.fold (fun s -> toBit >> (+) (s <<< 1)) 0s
    min (source |> f)
        (source |> Seq.rev |> f)


module Body =

  let toHash body = body |> Seq.head |> Border.toHash


module Tile =

  module Id =
    let get m = m.Id
    let set v m = { m with Id = v }
    let map = map get set
  module Body =
    let get m = m.Body
    let set v m = { m with Body = v }
    let map = map get set

  let getBorders tile =
    let makeBorder f =
      (tile.Id,
       tile.Body |> f |> Body.toHash)
    seq {
      Seq.empty
      seq { Rotate }
      seq { Rotate; Rotate }
      seq { Rotate; Rotate; Rotate }
    }
    |> Seq.map (Transform.reduce >> makeBorder)

  let orientTopLeftCorner matchedBorderHashes tile =
    List.empty
    |> Seq.unfold (fun ma -> Some (ma, Rotate :: ma))
    |> Seq.map
      (Transform.reduce
       >> Body.map
       >> (fun f -> f tile)
       >> Pair.ofSingle)
    |> SeqPair.map2
      (Body.get
       >> Body.toHash
       >> flip List.contains matchedBorderHashes
       >> function true -> 0 | false -> 1)
    |> SeqPair.scan2 (+) 0
    |> SeqPair.filter2 ((=) 2)
    |> Seq.map fst
    |> Seq.head

  let areHorizontalMatch left right =
    (=) (seq { Rotate }       |> flip Transform.reduce left  |> Body.toHash)
        (seq { Flip; Rotate } |> flip Transform.reduce right |> Body.toHash)

  let areVerticalMatch top bottom =
    (=) (seq { Flip; Rotate; Rotate } |> flip Transform.reduce top |> Body.toHash)
                                                           (bottom |> Body.toHash)


let getBorderPairings =
  Seq.collect Tile.getBorders
  >> Seq.groupBy snd
  >> SeqPair.map2 (Seq.map fst >> Seq.toArray)
  >> SeqPair.filter2 (Array.length >> (=) 2) // remove the unmatched border hashes
  >> SeqPair.map2 Array.toSeq
  >> Map

let getNextTile
    (tilesById: Map<TileId, Tile>)
    (tileIdsByBorderHash: Map<BorderHash, TileId seq>)
    (hashPreviousTile: Tile -> BorderHash)
    (areMatch: Tile -> Tile -> bool)
    (previousTile: Tile) =
  option {
    let hash = previousTile |> hashPreviousTile
    let! tileIds = tileIdsByBorderHash |> Map.tryFind hash
    let! nextTileId =
      tileIds
      |> Seq.filter ((<>) previousTile.Id)
      |> Seq.tryHead
    let! nextTile = tilesById |> Map.tryFind nextTileId
    return!
      seq {
        Seq.empty
        seq { Rotate }
        seq { Rotate; Rotate }
        seq { Rotate; Rotate; Rotate }
        seq { Flip }
        seq { Flip; Rotate }
        seq { Flip; Rotate; Rotate }
        seq { Flip; Rotate; Rotate; Rotate }
      }
      |> Seq.map (Transform.reduce >> Tile.Body.map >> (fun f -> f nextTile))
      |> Seq.filter (areMatch previousTile)
      |> Seq.tryHead
      |> Option.map Pair.ofSingle
  }

open FSharpPlus
let getTileCounts =
  Map.fold (fun s _ ->
    Seq.map (fun tId -> tId, 1)
    >> Map
    >> Map.unionWith (+) s) Map.empty

let arrange tilesById =
  let tileIdsByBorderHash = tilesById |> Map.values |> getBorderPairings
  let anchorId = tileIdsByBorderHash |> getTileCounts |> Map.toSeq |> Seq.minBy snd |> fst
  let anchor =
    tilesById
    |> Map.find anchorId
    |> Tile.orientTopLeftCorner (tileIdsByBorderHash |> Seq.map Kvp.key |> Seq.toList)

  let getNextTile = getNextTile tilesById tileIdsByBorderHash

  let gen areMatch transforms anchor =
    let hashPreviousTile = transforms |> Transform.reduce |> Tile.Body.map >> Tile.Body.get >> Body.toHash
    let areMatch = areMatch |> Func2.uncurry << Pair.mapAll Tile.Body.get |> Func2.curry
    anchor
    |> Seq.unfold (getNextTile hashPreviousTile areMatch)
    |> Seq.append (Seq.singleton anchor)
    |> Seq.toArray

  anchor
  |> gen Tile.areVerticalMatch [ Rotate ]
  |> Array.map (gen Tile.areHorizontalMatch [ Rotate; Rotate ])

module Parse =
  let parsePixel =
    function
    | '.' -> White
    | '#' -> Black
    | _ -> failwith "Invalid tile"

  let parseBody =
    Seq.map (Seq.map parsePixel >> Seq.cache)
    >> Seq.cache

  let parseId input =
    let regex = Regex.Match (input, "Tile (\d+):")
    regex.Groups.[1].Value |> int

  let parseTile input =
    { Id = input |> Seq.head |> parseId
      Body = input |> Seq.tail |> parseBody }

  let parse input =
    Regex.Split(input, "\r\n\r\n")
    |> Seq.map ((fun input -> Regex.Split (input, "\r\n")) >> parseTile >> fun t -> t.Id, t)
    |> Map

let toChar =
  function
  | White -> '.'
  | Black -> '#'

let printColors =
  Seq.map (
    Seq.chunkBySize 10
    >> Seq.collect (Seq.map toChar >> Seq.append (Seq.singleton '|'))
    >> System.String.Concat)
  >> Seq.chunkBySize 10
  >> Seq.collect (Seq.append (Seq.singleton ""))
  >> Seq.iter (printfn "%s")

let print t =
  printfn "Tile %A:" t.Id
  t.Body |> printColors

let merge (tiles: Tile array array) =
  let h = tiles.[0].[0].Body |> Seq.length
  let w = tiles.[0].[0].Body |> Seq.head |> Seq.length
  let result = Array.init (tiles |> Array.length |> (*) h) (fun _ ->
    Array.zeroCreate<Color> (tiles.[0] |> Array.length |> (*) w))
  tiles |> Array.iteri (fun i ->
    Array.iteri (fun j t ->
      tiles.[i].[j].Body
      |> Seq.iteri (fun x ->
        Seq.iteri (fun y c ->
          result.[i * h + x].[j * w + y] <- c
        ))))
  result |> Seq.map Array.toSeq

open System.IO
let run () =
  File.ReadAllText "input/Day20test.txt"
  |> Parse.parse
  |> arrange
  |> merge
  |> printColors