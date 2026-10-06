(* json2dir: create the directory tree a JSON document describes, in the current directory.
   Implements RFC J2D-1 (https://github.com/kitsunoff/awesome-json2dir/blob/main/spec/rfc-json2dir.md).
   Standard ML, Basis Library only (including the optional Posix structures). *)

exception Bad of string
fun fail msg = raise Bad msg

(* The document. Strings hold raw UTF-8 bytes (SML chars are 8-bit). *)
datatype json =
    Str of string
  | Arr of json list
  | Obj of (string * json) list

(* ---- §3: strict UTF-8 ---- *)

fun checkUtf8 (v : Word8Vector.vector) =
  let
    val n = Word8Vector.length v
    fun b i = if i < n then Word8.toInt (Word8Vector.sub (v, i)) else ~1
    fun cont i = let val c = b i in c >= 0x80 andalso c <= 0xBF end
    fun inRange i lo hi = let val c = b i in c >= lo andalso c <= hi end
    fun go i =
      if i >= n then ()
      else
        let val c = b i in
          if c < 0x80 then go (i + 1)
          else if c >= 0xC2 andalso c <= 0xDF andalso cont (i + 1) then go (i + 2)
          else if c = 0xE0 andalso inRange (i + 1) 0xA0 0xBF andalso cont (i + 2) then go (i + 3)
          else if ((c >= 0xE1 andalso c <= 0xEC) orelse c = 0xEE orelse c = 0xEF)
                  andalso cont (i + 1) andalso cont (i + 2) then go (i + 3)
          else if c = 0xED andalso inRange (i + 1) 0x80 0x9F andalso cont (i + 2) then go (i + 3)
          else if c = 0xF0 andalso inRange (i + 1) 0x90 0xBF andalso cont (i + 2) andalso cont (i + 3)
            then go (i + 4)
          else if c >= 0xF1 andalso c <= 0xF3 andalso cont (i + 1) andalso cont (i + 2) andalso cont (i + 3)
            then go (i + 4)
          else if c = 0xF4 andalso inRange (i + 1) 0x80 0x8F andalso cont (i + 2) andalso cont (i + 3)
            then go (i + 4)
          else fail "input is not valid UTF-8"
        end
  in
    go 0
  end

(* ---- §3: strict JSON parser over the input bytes ---- *)

fun encodeUtf8 cp =
  let
    val ch = Char.chr
    fun w x = Word.fromInt x
    fun i x = Word.toInt x
    val c = w cp
    val orb = Word.orb and andb = Word.andb and >> = Word.>>
  in
    if cp < 0x80 then [ch cp]
    else if cp < 0x800 then
      [ch (i (orb (0wxC0, >> (c, 0w6)))), ch (i (orb (0wx80, andb (c, 0wx3F))))]
    else if cp < 0x10000 then
      [ch (i (orb (0wxE0, >> (c, 0w12)))), ch (i (orb (0wx80, andb (>> (c, 0w6), 0wx3F)))),
       ch (i (orb (0wx80, andb (c, 0wx3F))))]
    else
      [ch (i (orb (0wxF0, >> (c, 0w18)))), ch (i (orb (0wx80, andb (>> (c, 0w12), 0wx3F)))),
       ch (i (orb (0wx80, andb (>> (c, 0w6), 0wx3F)))), ch (i (orb (0wx80, andb (c, 0wx3F))))]
  end

fun parse (v : Word8Vector.vector) : json =
  let
    val n = Word8Vector.length v
    val pos = ref 0
    fun peek () = if !pos < n then Word8.toInt (Word8Vector.sub (v, !pos)) else ~1
    fun bad what = fail ("input is not valid JSON: " ^ what ^ " at byte " ^ Int.toString (!pos))
    fun skipWs () =
      case peek () of
        0x20 => (pos := !pos + 1; skipWs ())
      | 0x09 => (pos := !pos + 1; skipWs ())
      | 0x0A => (pos := !pos + 1; skipWs ())
      | 0x0D => (pos := !pos + 1; skipWs ())
      | _ => ()
    fun expect c = if peek () = c then pos := !pos + 1 else bad ("expected '" ^ str (Char.chr c) ^ "'")
    fun hex4 () =
      let
        fun digit () =
          let val c = peek () in
            pos := !pos + 1;
            if c >= 0x30 andalso c <= 0x39 then c - 0x30
            else if c >= 0x61 andalso c <= 0x66 then c - 0x61 + 10
            else if c >= 0x41 andalso c <= 0x46 then c - 0x41 + 10
            else bad "bad \\u escape"
          end
        val a = digit (); val b = digit (); val c = digit (); val d = digit ()
      in
        ((a * 16 + b) * 16 + c) * 16 + d
      end
    fun parseString () =
      let
        val () = expect 0x22
        fun loop acc =
          let val c = peek () in
            if c = ~1 then bad "unterminated string"
            else if c = 0x22 then (pos := !pos + 1; String.implode (rev acc))
            else if c < 0x20 then bad "control character in string"
            else if c = 0x5C then
              let
                val () = pos := !pos + 1
                val e = peek ()
                val () = pos := !pos + 1
              in
                case e of
                  0x22 => loop (#"\"" :: acc)
                | 0x5C => loop (#"\\" :: acc)
                | 0x2F => loop (#"/" :: acc)
                | 0x62 => loop (#"\b" :: acc)
                | 0x66 => loop (#"\f" :: acc)
                | 0x6E => loop (#"\n" :: acc)
                | 0x72 => loop (#"\r" :: acc)
                | 0x74 => loop (#"\t" :: acc)
                | 0x75 =>
                    let
                      val u = hex4 ()
                      val cp =
                        if u >= 0xD800 andalso u <= 0xDBFF then
                          if peek () = 0x5C andalso !pos + 1 < n
                             andalso Word8Vector.sub (v, !pos + 1) = 0wx75 then
                            let
                              val () = pos := !pos + 2
                              val lo = hex4 ()
                            in
                              if lo >= 0xDC00 andalso lo <= 0xDFFF
                              then 0x10000 + (u - 0xD800) * 0x400 + (lo - 0xDC00)
                              else fail "string contains an unpaired surrogate"
                            end
                          else fail "string contains an unpaired surrogate"
                        else if u >= 0xDC00 andalso u <= 0xDFFF then
                          fail "string contains an unpaired surrogate"
                        else u
                    in
                      loop (List.revAppend (encodeUtf8 cp, acc))
                    end
                | _ => bad "bad escape"
              end
            else (pos := !pos + 1; loop (Char.chr c :: acc))
          end
      in
        loop []
      end
    fun parseValue () =
      (skipWs ();
       case peek () of
         0x22 => Str (parseString ())
       | 0x7B => parseObject ()
       | 0x5B => parseArray ()
       | ~1 => bad "unexpected end of input"
       | c =>
           if c = 0x74 orelse c = 0x66 orelse c = 0x6E orelse c = 0x2D orelse (c >= 0x30 andalso c <= 0x39)
           then fail "numbers, booleans and null are not allowed"
           else bad "unexpected character")
    and parseObject () =
      let
        val () = expect 0x7B
        val () = skipWs ()
        fun member () =
          let
            val () = skipWs ()
            val k = if peek () = 0x22 then parseString () else bad "expected a member name"
            val () = skipWs ()
            val () = expect 0x3A
            val x = parseValue ()
            val () = skipWs ()
          in
            (k, x)
          end
        fun loop acc =
          let val m = member () in
            case peek () of
              0x2C => (pos := !pos + 1; loop (m :: acc))
            | 0x7D => (pos := !pos + 1; rev (m :: acc))
            | _ => bad "expected ',' or '}'"
          end
      in
        if peek () = 0x7D then (pos := !pos + 1; Obj []) else Obj (loop [])
      end
    and parseArray () =
      let
        val () = expect 0x5B
        val () = skipWs ()
        fun loop acc =
          let val x = parseValue () val () = skipWs () in
            case peek () of
              0x2C => (pos := !pos + 1; loop (x :: acc))
            | 0x5D => (pos := !pos + 1; rev (x :: acc))
            | _ => bad "expected ',' or ']'"
          end
      in
        if peek () = 0x5D then (pos := !pos + 1; Arr []) else Arr (loop [])
      end
    (* §3: a leading byte order mark may be ignored. *)
    val () =
      if n >= 3 andalso Word8Vector.sub (v, 0) = 0wxEF andalso Word8Vector.sub (v, 1) = 0wxBB
         andalso Word8Vector.sub (v, 2) = 0wxBF then pos := 3 else ()
    val doc = parseValue ()
    val () = skipWs ()
  in
    if !pos <> n then bad "trailing data" else doc
  end

(* ---- §4, §6: validation, done for the whole document before anything is written ---- *)

fun hasChar c s = CharVector.exists (fn x => x = c) s

(* Sort members by the bytes of their names (stable), keep the last of duplicates. *)
fun members (ms : (string * json) list) =
  let
    fun merge ([], ys) = ys
      | merge (xs, []) = xs
      | merge (x :: xs, y :: ys) =
          if String.compare (#1 y, #1 x) = LESS then y :: merge (x :: xs, ys)
          else x :: merge (xs, y :: ys)
    fun sort [] = []
      | sort [x] = [x]
      | sort xs =
          let val h = length xs div 2 in
            merge (sort (List.take (xs, h)), sort (List.drop (xs, h)))
          end
    fun lastOf (a :: (rest as b :: _)) = if #1 a = #1 b then lastOf rest else a :: lastOf rest
      | lastOf xs = xs
  in
    lastOf (sort ms)
  end

fun validate where_ (x : json) =
  case x of
    Str _ => ()
  | Arr [Str "link", Str t] =>
      if hasChar #"\000" t then fail (where_ ^ ": a link target cannot contain NUL") else ()
  | Arr [Str "script", Str _] => ()
  | Arr [Str k, Str _] => fail (where_ ^ ": unknown array kind \"" ^ k ^ "\"")
  | Arr _ => fail (where_ ^ ": an array must be [\"link\", target] or [\"script\", content]")
  | Obj ms =>
      List.app
        (fn (name, child) =>
           let val p = if where_ = "." then name else where_ ^ "/" ^ name in
             if name = "" orelse name = "." orelse name = ".." orelse hasChar #"/" name
                orelse hasChar #"\000" name
             then fail (p ^ ": invalid name")
             else validate p child
           end)
        ms

(* ---- §5: writing the tree ---- *)

structure FS = Posix.FileSys

fun lstatOpt p =
  SOME (FS.lstat p)
  handle e as OS.SysErr (_, SOME err) => if err = Posix.Error.noent then NONE else raise e

(* §5.2, §5.3: an existing non-directory (a symlink itself, never its target) is removed;
   §5.4: a directory in the way of a non-object is an error. *)
fun clear p NONE = ()
  | clear p (SOME st) = if FS.ST.isDir st then fail (p ^ ": a directory is in the way") else FS.unlink p

fun writeAll fd s =
  let
    val v = Byte.stringToBytes s
    fun go off =
      if off < Word8Vector.length v then
        go (off + Posix.IO.writeVec (fd, Word8VectorSlice.slice (v, off, NONE)))
      else ()
  in
    go 0
  end

(* createf = O_CREAT; with O_EXCL it never opens an existing entry and never follows a final
   symlink (POSIX), so no O_NOFOLLOW is needed (the Basis O structure does not offer one). *)
fun writeFile p content executable =
  let
    val mode666 = FS.S.flags [FS.S.irusr, FS.S.iwusr, FS.S.irgrp, FS.S.iwgrp, FS.S.iroth, FS.S.iwoth]
    val fd = FS.createf (p, FS.O_WRONLY, FS.O.excl, mode666)
    fun body () =
      (writeAll fd content;
       if executable then
         let
           val cur = FS.S.fromWord (SysWord.andb (FS.S.toWord (FS.ST.mode (FS.fstat fd)), 0wxFFF))
         in
           FS.fchmod (fd, FS.S.flags [cur, FS.S.ixusr, FS.S.ixgrp, FS.S.ixoth])
         end
       else ())
  in
    (body (); Posix.IO.close fd) handle e => (Posix.IO.close fd handle _ => (); raise e)
  end

fun apply dir ms =
  List.app
    (fn (name, x) =>
       let
         val p = if dir = "" then name else dir ^ "/" ^ name
         val existing = lstatOpt p
       in
         case x of
           Str s => (clear p existing; writeFile p s false)
         | Arr [Str "link", Str t] => (clear p existing; FS.symlink {old = t, new = p})
         | Arr [_, Str c] => (clear p existing; writeFile p c true)
         | Arr _ => fail "unreachable"
         | Obj children =>
             ((case existing of
                 SOME st =>
                   if FS.ST.isDir st then ()
                   else (FS.unlink p; FS.mkdir (p, FS.S.flags [FS.S.irwxu, FS.S.irwxg, FS.S.irwxo]))
               | NONE => FS.mkdir (p, FS.S.flags [FS.S.irwxu, FS.S.irwxg, FS.S.irwxo]));
              apply p children)
       end)
    ms

(* Sort and de-duplicate every object once, up front. *)
fun normalize (Obj ms) = Obj (map (fn (k, x) => (k, normalize x)) (members ms))
  | normalize x = x

(* All of stdin as bytes, read with Posix.IO.readVec. *)
fun readStdin () =
  let
    fun go acc =
      let val v = Posix.IO.readVec (Posix.FileSys.stdin, 65536) in
        if Word8Vector.length v = 0 then Word8Vector.concat (rev acc) else go (v :: acc)
      end
  in
    go []
  end

fun main () =
  case CommandLine.arguments () of
    _ :: _ => (TextIO.output (TextIO.stdErr, "usage: json2dir < document.json\n"); TextIO.flushOut TextIO.stdErr; Posix.Process.exit 0w2)
  | [] =>
      let
        val input = readStdin ()
        val () = checkUtf8 input
        val doc = normalize (parse input)
        val () = case doc of Obj _ => () | _ => fail "the root of the document must be an object"
        val () = validate "." doc
      in
        case doc of Obj ms => apply "" ms | _ => ();
        OS.Process.exit OS.Process.success
      end
      handle Bad msg => (TextIO.output (TextIO.stdErr, "json2dir: " ^ msg ^ "\n"); OS.Process.exit OS.Process.failure)
           | OS.SysErr (msg, _) => (TextIO.output (TextIO.stdErr, "json2dir: " ^ msg ^ "\n"); OS.Process.exit OS.Process.failure)
           | e => (TextIO.output (TextIO.stdErr, "json2dir: " ^ exnMessage e ^ "\n"); OS.Process.exit OS.Process.failure)

val () = main ()
