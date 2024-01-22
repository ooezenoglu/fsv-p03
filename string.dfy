method arraycopy<E>(from: array<E>, from_pos: nat,
                    to:   array<E>, to_pos:   nat,
                    length: nat)
  requires from_pos + length <= from.Length
  requires to_pos + length <= to.Length
  modifies to

  requires to != from

  // first part: unchanged
  ensures to[..to_pos] == old(to[..to_pos])

  // second part: copied
  ensures to[to_pos..to_pos+length] == from[from_pos..from_pos+length]

  // third part: unchanged
  ensures to[to_pos+length..] == old(to[to_pos+length..])
{
  var i := 0;
  while i < length
    invariant i <= length
    invariant to[..to_pos] == old(to[..to_pos])
    invariant to[to_pos+length..] == old(to[to_pos+length..])
    invariant to[to_pos..to_pos+i] == from[from_pos..from_pos+i]
    decreases length - i
    modifies to
  {
    to[to_pos+i] := from[from_pos+i];
    i := i+1;
  }
}

// Here, <E(==)> is indicates the generic type of elements,
// but we require that elements must be comparable by equality.
// You can ignore this technical detail.
method arraycompare<E(==)>(a: array<E>, a_pos: nat,
                          b: array<E>, b_pos: nat,
                          length: nat)
  returns (eq: bool)
  requires a_pos + length <= a.Length && b_pos + length <= b.Length
  ensures eq <==> forall i :: a_pos <= i < a_pos + length ==> a[i] == b[b_pos + i - a_pos]
{
  eq := true;
  var i := 0;
  while i < length
    invariant 0 <= i <= length
    invariant eq <==> forall j :: a_pos <= j < a_pos + i ==> a[j] == b[b_pos + j - a_pos]
  {
    if a[a_pos + i] != b[b_pos + i] {
      eq := false;
      break;
    }
    i := i + 1;
  }
}


class String {
  // model variable
  ghost var content: seq<char>

  // class attribtues of the implementation
  var chars: array<char>
  var start: int
  var end: int

  ghost predicate inv()
    reads this, chars
  {
    0 <= start && start <= end && end <= chars.Length &&
    content == chars[start..end]
  }
  
  
  constructor(chars: array<char>, start: int, end: int)
    requires 0 <= start && start <= end && end <= chars.Length
    ensures content == chars[start..end]
    ensures inv()
  {
    this.chars := chars;
    this.start := start;
    this.end   := end;
    this.content := chars[start..end];
  }
  
  
  method Length()
    returns (n: int)
    requires inv()
    ensures n == |content|
  {
    return end - start;
  }
  
  
  lemma helper(at: int, k: int)
    requires 0 <= at <= k <= end - start
    requires inv()
    ensures content[at..k] == chars[start + at..start + k]
  {
    if (at < k) { helper(at, k - 1); }
  }
  
  method Substring(at: int, length: int)
    returns (result: String)
    requires inv()
    requires 0 <= at && at <= |content|  
    requires 0 <= length && at + length <= |content|  
    ensures result.inv()
    ensures result.content == content[at..at + length]
  {
    helper(at, at + length);
    return new String(chars, start + at, start + at + length);
  }
  
  
  method Concat(that: String)
    returns (result: String)
    requires inv() && that.inv()
    ensures result.inv()
    ensures result.content == this.content + that.content
  {
    var m := this.Length();
    var n := that.Length();
    var newchars := new char[m + n];
  
    // Copy contents of this.chars to newchars
    arraycopy(this.chars, start, newchars, 0, m);
    assert newchars[0..m] == this.chars[start..start + m];
  
    // Copy contents of that.chars to newchars
    arraycopy(that.chars, that.start, newchars, m, n);
    assert newchars[m..m + n] == that.chars[that.start..that.start + n];
  
    // Construct the new String object
    result := new String(newchars, 0, m + n);
  
    // Assert that result.content is the concatenation of this.content and that.content
    assert result.content == newchars[0..m + n];
    assert result.content == this.chars[start..start + m] + that.chars[that.start..that.start + n];
    assert result.content == this.content + that.content;
    return result;
  }
  
  
  
  method ContainsAt(that: String, at: int)
    returns (result: bool)
    requires inv() && that.inv() && 0 <= at && at <= |content|
    ensures result <==> at + |that.content| <= |content| && content[at..at + |that.content|] == that.content
  {
    var thisLength := this.end - this.start;
    var thatLength := that.end - that.start;
    
    if at + thatLength <= thisLength {
      var eq := arraycompare(chars, start + at, that.chars, that.start, thatLength);
      helper(at, at + thatLength);
      return eq;
    } else {
      return false;
    }
  }
  
}
