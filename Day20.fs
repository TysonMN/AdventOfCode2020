module Day20

open System.Text.RegularExpressions

type Color = Black | White
type Id = int
type Tile = {
  Id: Id
  Body: Color seq seq
}

type Side = Top | Right | Bottom | Left
type Flip = Original | Inverted
type Orientation = {
  Side: Side
  Flip: Flip
}

type Transform =
  | RotateRight
  | RotateLeft
  | FlipVertical
  | FlipHorizontal

module Orientation =

  let sides = [| Top; Right; Bottom; Left |]
  let normalizeIndex i = FSharpPlus.Math.Generic.remE i 4
  let shift offset side =
    sides
    |> Array.findIndex ((=) side) |> (+) offset
    |> normalizeIndex
    |> Array.get sides
  let private right = shift -1
  let private left  = shift +1

  let distance s1 s2 =
    (sides |> Array.findIndex ((=) s1))
    - (sides |> Array.findIndex ((=) s2))
    |> normalizeIndex

  let rotateRight o = { o with Side = right o.Side }
  let rotateLeft o = { o with Side = left o.Side }

  let private toggleFlip f = if f = Original then Inverted else Original
  let private invertSide a b s =
    if   s = a then b
    elif s = b then a
    else s
  let private flip s1 s2 o = { Flip = toggleFlip o.Flip; Side = invertSide s1 s2 o.Side }
  let opposite o = { o with Side = shift 2 o.Side; Flip = toggleFlip o.Flip }

  let flipVertical = flip Top Bottom
  let flipHorizontal = flip Left Right

  let getTransforms anchor =
    let rec loop o =
      if anchor = o then []
      elif anchor.Flip <> o.Flip then
        if   (o.Side = Top  && anchor.Side = Bottom) || (o.Side = Bottom && anchor.Side = Top ) then FlipVertical :: loop (flipVertical o)
        elif (o.Side = Left && anchor.Side = Right ) || (o.Side = Right  && anchor.Side = Left) then FlipHorizontal :: loop (flipHorizontal o)
        elif distance anchor.Side o.Side = 1 then RotateRight :: loop (rotateRight o)
        else RotateLeft :: loop (rotateLeft o)
      elif distance anchor.Side o.Side = 1 then RotateLeft :: loop (rotateLeft o)
      else RotateRight :: loop (rotateRight o)
    loop

module Tile =
  let transform t =
    Seq.map (fun x -> printfn "Transforming title %A with %A" t.Id x; x)
    >> Seq.fold (fun body ->
      (function
      | RotateRight    -> Seq.transpose >> Seq.rev
      | RotateLeft     -> Seq.transpose << Seq.rev
      | FlipVertical   -> Seq.rev
      | FlipHorizontal -> Seq.map Seq.rev)
      >> (fun f -> f body)) t.Body
    >> fun body -> { t with Body = body }

type Hash = int16
type Border = {
  TileId: Id
  Orientation: Orientation
  Hash: Hash
}

module Border =
  let toBit =
    function Black -> 1s | White -> 0s
  let getBorderHash =
    Seq.fold (fun s -> toBit >> (+) (s <<< 1)) 0s

let getBorders { Id = id; Body = body } =
  let makeBorder o s f = {
    TileId = id
    Orientation = { Side = s; Flip = o; }
    Hash = body |> f |> Border.getBorderHash
  }
  seq {
    makeBorder Original Top Seq.head
    makeBorder Original Left (Seq.map Seq.head)
    makeBorder Original Bottom Seq.last
    makeBorder Original Right (Seq.map Seq.last)
    makeBorder Inverted Top (Seq.head >> Seq.rev)
    makeBorder Inverted Left (Seq.map Seq.head >> Seq.rev)
    makeBorder Inverted Bottom (Seq.last >> Seq.rev)
    makeBorder Inverted Right (Seq.map Seq.last >> Seq.rev)
  }

open FSharpPlus

let getBorderPairings =
  Seq.collect getBorders
  >> Seq.groupBy (fun b -> b.Hash)
  >> Seq.map (Tuple2.mapItem2 Seq.toArray)
  >> Map
  >> Map.filter (fun _ -> Array.length >> (=) 2)
  >> Map.mapValues Array.toSeq

let getTileCounts =
  Map.fold (fun s _ ->
    Seq.map (fun b -> b.TileId, 1)
    >> Map
    >> Map.unionWith (+) s) Map.empty

let getSharedBorders t1 t2 =
  query {
    for b1 in getBorders t1 do
    for b2 in getBorders t2 do
    where (b1.Hash = b2.Hash)
    head // possibly a bug
  }

let getAdjacentBorders borderPairings tile =
  getBorders tile
  |> Seq.choose (fun b -> borderPairings |> Map.tryFind b.Hash)
  |> Seq.collect id
  |> Seq.filter (fun b -> b.TileId <> tile.Id)

let tryGetAdjacentOppositeBorderPair (borderPairings: (Hash, _ seq) Map) side tile =
  query {
    for b in getBorders tile do
    where (b.Orientation.Side = side)
    for bs in borderPairings |> Map.tryFind b.Hash |> Option.toArray do
    for b' in bs do
    where (b'.TileId <> b.TileId)
    select (b, b')
  }
  |> tryHead

let getNextTile tileMap borderPairings direction prev =
  monad {
    let! (prevBorder, nextBorder) = tryGetAdjacentOppositeBorderPair borderPairings direction prev
    let! nextTile = tileMap |> Map.tryFind nextBorder.TileId
    let result =
      Orientation.opposite nextBorder.Orientation
      |> Orientation.getTransforms prevBorder.Orientation 
      |> Tile.transform nextTile
    return result, result
  }

let arrange tileMap =
  let borderPairings = tileMap |> Map.values |> getBorderPairings
  let anchorId = borderPairings |> getTileCounts |> Map.toSeq |> Seq.minBy snd |> fst
  let anchor = tileMap |> Map.find anchorId

  // Below line is hardcoded for sample solution; replace with setup code
  let anchor = Tile.transform anchor [FlipVertical]

  let getNextTile = getNextTile tileMap borderPairings

  let gen direction anchor =
    anchor
    |> Seq.unfold (getNextTile direction)
    |> Seq.append (Seq.singleton anchor)
    |> Seq.toArray

  // let it rip
  anchor
  |> gen Bottom
  |> Array.map (gen Right)

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

open System
open System.IO
let run () =
  File.ReadAllText "input/Day20test.txt"
  |> Parse.parse
  |> arrange
  |> merge
  |> printColors