def main : IO Unit := do
  let input <- IO.FS.readFile "../input"
  let lines := input.splitOn "\n"
  let pairs := (lines.filter (fun line => not line.isEmpty)).map (
    fun line => match (line.splitOn "   ").map (String.toInt!) with
    | x :: [y] => (x, y)
    | lst => panic s!"not a pair {lst} from {line}")

  let (xs, ys) := pairs.unzip
  let xss := xs.mergeSort
  let yss := ys.mergeSort
  let ps: List (Int × Int) := xss.zip yss
  let ds := ps.map (fun (x, y) => (x - y).natAbs)
  let res1 := ds.foldl Nat.add 0
  IO.println s!"part 1: {res1}"

  let dd := xss.map (fun x => x * yss.count x)
  let res2 := dd.foldl (· + ·) 0
  IO.println s!"part 2: {res2}"
