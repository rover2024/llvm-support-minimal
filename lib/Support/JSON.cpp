//=== JSON.cpp - JSON value, parsing and serialization - C++ -----------*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===---------------------------------------------------------------------===//

#include "llvm/Support/JSON.h"
#include "llvm/ADT/ArrayRef.h"
// #include "llvm/ADT/STLExtras.h"
// #include "llvm/ADT/StringExtras.h"
#include "llvm/Support/ConvertUTF.h"
#include "llvm/ADT/bit.h"
// #include "llvm/Support/Error.h"
// #include "llvm/Support/Format.h"
// #include "llvm/Support/NativeFormatting.h"
// #include "llvm/Support/raw_ostream.h"
#include <cctype>
#include <cerrno>
#include <optional>
#include <sstream>

namespace llvm {
namespace json {

Value &Object::operator[](const ObjectKey &K) {
  return try_emplace(K, nullptr).first->second;
}
Value &Object::operator[](ObjectKey &&K) {
  return try_emplace(std::move(K), nullptr).first->second;
}
Value *Object::get(StringRef K) {
  auto I = find(K);
  if (I == end())
    return nullptr;
  return &I->second;
}
const Value *Object::get(StringRef K) const {
  auto I = find(K);
  if (I == end())
    return nullptr;
  return &I->second;
}
std::optional<std::nullptr_t> Object::getNull(StringRef K) const {
  if (auto *V = get(K))
    return V->getAsNull();
  return std::nullopt;
}
std::optional<bool> Object::getBoolean(StringRef K) const {
  if (auto *V = get(K))
    return V->getAsBoolean();
  return std::nullopt;
}
std::optional<double> Object::getNumber(StringRef K) const {
  if (auto *V = get(K))
    return V->getAsNumber();
  return std::nullopt;
}
std::optional<int64_t> Object::getInteger(StringRef K) const {
  if (auto *V = get(K))
    return V->getAsInteger();
  return std::nullopt;
}
std::optional<llvm::StringRef> Object::getString(StringRef K) const {
  if (auto *V = get(K))
    return V->getAsString();
  return std::nullopt;
}
const json::Object *Object::getObject(StringRef K) const {
  if (auto *V = get(K))
    return V->getAsObject();
  return nullptr;
}
json::Object *Object::getObject(StringRef K) {
  if (auto *V = get(K))
    return V->getAsObject();
  return nullptr;
}
const json::Array *Object::getArray(StringRef K) const {
  if (auto *V = get(K))
    return V->getAsArray();
  return nullptr;
}
json::Array *Object::getArray(StringRef K) {
  if (auto *V = get(K))
    return V->getAsArray();
  return nullptr;
}
bool operator==(const Object &LHS, const Object &RHS) {
  if (LHS.size() != RHS.size())
    return false;
  for (const auto &L : LHS) {
    auto R = RHS.find(L.first);
    if (R == RHS.end() || L.second != R->second)
      return false;
  }
  return true;
}

Array::Array(std::initializer_list<Value> Elements) {
  V.reserve(Elements.size());
  for (const Value &V : Elements) {
    emplace_back(nullptr);
    back().moveFrom(std::move(V));
  }
}

Value::Value(std::initializer_list<Value> Elements)
    : Value(json::Array(Elements)) {}

void Value::copyFrom(const Value &M) {
  Type = M.Type;
  switch (Type) {
  case T_Null:
  case T_Boolean:
  case T_Double:
  case T_Integer:
  case T_UINT64:
    memcpy(&Union, &M.Union, sizeof(Union));
    break;
  case T_StringRef:
    create<StringRef>(M.as<StringRef>());
    break;
  case T_String:
    create<std::string>(M.as<std::string>());
    break;
  case T_Object:
    create<json::Object>(M.as<json::Object>());
    break;
  case T_Array:
    create<json::Array>(M.as<json::Array>());
    break;
  }
}

void Value::moveFrom(const Value &&M) {
  Type = M.Type;
  switch (Type) {
  case T_Null:
  case T_Boolean:
  case T_Double:
  case T_Integer:
  case T_UINT64:
    memcpy(&Union, &M.Union, sizeof(Union));
    break;
  case T_StringRef:
    create<StringRef>(M.as<StringRef>());
    break;
  case T_String:
    create<std::string>(std::move(M.as<std::string>()));
    M.Type = T_Null;
    break;
  case T_Object:
    create<json::Object>(std::move(M.as<json::Object>()));
    M.Type = T_Null;
    break;
  case T_Array:
    create<json::Array>(std::move(M.as<json::Array>()));
    M.Type = T_Null;
    break;
  }
}

void Value::destroy() {
  switch (Type) {
  case T_Null:
  case T_Boolean:
  case T_Double:
  case T_Integer:
  case T_UINT64:
    break;
  case T_StringRef:
    as<StringRef>().~StringRef();
    break;
  case T_String:
    as<std::string>().~basic_string();
    break;
  case T_Object:
    as<json::Object>().~Object();
    break;
  case T_Array:
    as<json::Array>().~Array();
    break;
  }
}

void Value::print(std::ostream &OS) const { OS << *this; }

bool operator==(const Value &L, const Value &R) {
  if (L.kind() != R.kind())
    return false;
  switch (L.kind()) {
  case Value::Null:
    return *L.getAsNull() == *R.getAsNull();
  case Value::Boolean:
    return *L.getAsBoolean() == *R.getAsBoolean();
  case Value::Number:
    // Workaround for https://gcc.gnu.org/bugzilla/show_bug.cgi?id=323
    // The same integer must convert to the same double, per the standard.
    // However we see 64-vs-80-bit precision comparisons with gcc-7 -O3 -m32.
    // So we avoid floating point promotion for exact comparisons.
    if (L.Type == Value::T_Integer || R.Type == Value::T_Integer)
      return L.getAsInteger() == R.getAsInteger();
    return *L.getAsNumber() == *R.getAsNumber();
  case Value::String:
    return *L.getAsString() == *R.getAsString();
  case Value::Array:
    return *L.getAsArray() == *R.getAsArray();
  case Value::Object:
    return *L.getAsObject() == *R.getAsObject();
  }
  llvm_unreachable("Unknown value kind");
}

void Path::report(llvm::StringLiteral Msg) {
  // Walk up to the root context, and count the number of segments.
  unsigned Count = 0;
  const Path *P;
  for (P = this; P->Parent != nullptr; P = P->Parent)
    ++Count;
  Path::Root *R = P->Seg.root();
  // Fill in the error message and copy the path (in reverse order).
  R->ErrorMessage = Msg;
  R->ErrorPath.resize(Count);
  auto It = R->ErrorPath.begin();
  for (P = this; P->Parent != nullptr; P = P->Parent)
    *It++ = P->Seg;
}

std::string Path::Root::getError() const {
  std::stringstream OS;
  OS << (ErrorMessage.empty() ? "invalid JSON contents" : ErrorMessage);
  if (ErrorPath.empty()) {
    if (!Name.empty())
      OS << " when parsing " << Name;
  } else {
    OS << " at " << (Name.empty() ? "(root)" : Name);
    for (auto It = ErrorPath.rbegin(); It != ErrorPath.rend(); ++It) {
      const Segment &S = *It;
      if (S.isField())
        OS << '.' << S.field();
      else
        OS << '[' << S.index() << ']';
    }
  }
  return OS.str();
}

std::vector<const Object::value_type *> sortedElements(const Object &O) {
  std::vector<const Object::value_type *> Elements;
  for (const auto &E : O)
    Elements.push_back(&E);
  std::sort(Elements.begin(), Elements.end(),
             [](const Object::value_type *L, const Object::value_type *R) {
               return L->first < R->first;
             });
  return Elements;
}

// Prints a one-line version of a value that isn't our main focus.
// We interleave writes to OS and JOS, exploiting the lack of extra buffering.
// This is OK as we own the implementation.
static void abbreviate(const Value &V, OStream &JOS) {
  switch (V.kind()) {
  case Value::Array:
    JOS.rawValue(V.getAsArray()->empty() ? "[]" : "[ ... ]");
    break;
  case Value::Object:
    JOS.rawValue(V.getAsObject()->empty() ? "{}" : "{ ... }");
    break;
  case Value::String: {
    llvm::StringRef S = *V.getAsString();
    if (S.size() < 40) {
      JOS.value(V);
    } else {
      std::string Truncated = fixUTF8(S.substr(0, 37));
      Truncated.append("...");
      JOS.value(Truncated);
    }
    break;
  }
  default:
    JOS.value(V);
  }
}

// Prints a semi-expanded version of a value that is our main focus.
// Array/Object entries are printed, but not recursively as they may be huge.
static void abbreviateChildren(const Value &V, OStream &JOS) {
  switch (V.kind()) {
  case Value::Array:
    JOS.array([&] {
      for (const auto &I : *V.getAsArray())
        abbreviate(I, JOS);
    });
    break;
  case Value::Object:
    JOS.object([&] {
      for (const auto *KV : sortedElements(*V.getAsObject())) {
        JOS.attributeBegin(KV->first);
        abbreviate(KV->second, JOS);
        JOS.attributeEnd();
      }
    });
    break;
  default:
    JOS.value(V);
  }
}

void Path::Root::printErrorContext(const Value &R, std::ostream &OS) const {
  OStream JOS(OS, /*IndentSize=*/2);
  // PrintValue recurses down the path, printing the ancestors of our target.
  // Siblings of nodes along the path are printed with abbreviate(), and the
  // target itself is printed with the somewhat richer abbreviateChildren().
  // 'Recurse' is the lambda itself, to allow recursive calls.
  auto PrintValue = [&](const Value &V, ArrayRef<Segment> Path, auto &Recurse) {
    // Print the target node itself, with the error as a comment.
    // Also used if we can't follow our path, e.g. it names a field that
    // *should* exist but doesn't.
    auto HighlightCurrent = [&] {
      std::string Comment = "error: ";
      Comment.append(ErrorMessage.data(), ErrorMessage.size());
      JOS.comment(Comment);
      abbreviateChildren(V, JOS);
    };
    if (Path.empty()) // We reached our target.
      return HighlightCurrent();
    const Segment &S = Path.back(); // Path is in reverse order.
    if (S.isField()) {
      // Current node is an object, path names a field.
      llvm::StringRef FieldName = S.field();
      const Object *O = V.getAsObject();
      if (!O || !O->get(FieldName))
        return HighlightCurrent();
      JOS.object([&] {
        for (const auto *KV : sortedElements(*O)) {
          JOS.attributeBegin(KV->first);
          if (FieldName == StringRef(KV->first))
            Recurse(KV->second, Path.drop_back(), Recurse);
          else
            abbreviate(KV->second, JOS);
          JOS.attributeEnd();
        }
      });
    } else {
      // Current node is an array, path names an element.
      const Array *A = V.getAsArray();
      if (!A || S.index() >= A->size())
        return HighlightCurrent();
      JOS.array([&] {
        unsigned Current = 0;
        for (const auto &V : *A) {
          if (Current++ == S.index())
            Recurse(V, Path.drop_back(), Recurse);
          else
            abbreviate(V, JOS);
        }
      });
    }
  };
  PrintValue(R, ErrorPath, PrintValue);
}

namespace {
// Simple recursive-descent JSON parser.
class Parser {
public:
  Parser(StringRef JSON)
      : Start(JSON.data()), P(JSON.data()), End(JSON.data() + JSON.size()) {}

  bool checkUTF8() {
    size_t ErrOffset;
    if (isUTF8(StringRef(Start, End - Start), &ErrOffset))
      return true;
    P = Start + ErrOffset; // For line/column calculation.
    return parseError("Invalid UTF-8 sequence");
  }

  bool parseValue(Value &Out);

  bool assertEnd() {
    eatWhitespace();
    if (P == End)
      return true;
    return parseError("Text after end of document");
  }

  ParseError takeError() {
    assert(Err);
    return std::move(*Err);
  }

private:
  void eatWhitespace() {
    while (P != End && (*P == ' ' || *P == '\r' || *P == '\n' || *P == '\t'))
      ++P;
  }

  // On invalid syntax, parseX() functions return false and set Err.
  bool parseNumber(char First, Value &Out);
  bool parseString(std::string &Out);
  bool parseUnicode(std::string &Out);
  bool parseError(const char *Msg); // always returns false

  char next() { return P == End ? 0 : *P++; }
  char peek() { return P == End ? 0 : *P; }
  static bool isNumber(char C) {
    return C == '0' || C == '1' || C == '2' || C == '3' || C == '4' ||
           C == '5' || C == '6' || C == '7' || C == '8' || C == '9' ||
           C == 'e' || C == 'E' || C == '+' || C == '-' || C == '.';
  }

  std::optional<ParseError> Err;
  const char *Start, *P, *End;
};
} // namespace

bool Parser::parseValue(Value &Out) {
  eatWhitespace();
  if (P == End)
    return parseError("Unexpected EOF");
  switch (char C = next()) {
  // Bare null/true/false are easy - first char identifies them.
  case 'n':
    Out = nullptr;
    return (next() == 'u' && next() == 'l' && next() == 'l') ||
           parseError("Invalid JSON value (null?)");
  case 't':
    Out = true;
    return (next() == 'r' && next() == 'u' && next() == 'e') ||
           parseError("Invalid JSON value (true?)");
  case 'f':
    Out = false;
    return (next() == 'a' && next() == 'l' && next() == 's' && next() == 'e') ||
           parseError("Invalid JSON value (false?)");
  case '"': {
    std::string S;
    if (parseString(S)) {
      Out = std::move(S);
      return true;
    }
    return false;
  }
  case '[': {
    Out = Array{};
    Array &A = *Out.getAsArray();
    eatWhitespace();
    if (peek() == ']') {
      ++P;
      return true;
    }
    for (;;) {
      A.emplace_back(nullptr);
      if (!parseValue(A.back()))
        return false;
      eatWhitespace();
      switch (next()) {
      case ',':
        eatWhitespace();
        continue;
      case ']':
        return true;
      default:
        return parseError("Expected , or ] after array element");
      }
    }
  }
  case '{': {
    Out = Object{};
    Object &O = *Out.getAsObject();
    eatWhitespace();
    if (peek() == '}') {
      ++P;
      return true;
    }
    for (;;) {
      if (next() != '"')
        return parseError("Expected object key");
      std::string K;
      if (!parseString(K))
        return false;
      eatWhitespace();
      if (next() != ':')
        return parseError("Expected : after object key");
      eatWhitespace();
      if (!parseValue(O[std::move(K)]))
        return false;
      eatWhitespace();
      switch (next()) {
      case ',':
        eatWhitespace();
        continue;
      case '}':
        return true;
      default:
        return parseError("Expected , or } after object property");
      }
    }
  }
  default:
    if (isNumber(C))
      return parseNumber(C, Out);
    return parseError("Invalid JSON value");
  }
}

bool Parser::parseNumber(char First, Value &Out) {
  // Read the number into a string. (Must be null-terminated for strto*).
  SmallVector<char, 24> S;
  S.push_back(First);
  while (isNumber(peek()))
    S.push_back(next());

  S.push_back(0);
  S.pop_back();
    
  char *End;
  // Try first to parse as integer, and if so preserve full 64 bits.
  // We check for errno for out of bounds errors and for End == S.end()
  // to make sure that the numeric string is not malformed.
  errno = 0;
  int64_t I = std::strtoll(S.data(), &End, 10);
  if (End == S.end() && errno != ERANGE) {
    Out = I;
    return true;
  }
  // strtroull has a special handling for negative numbers, but in this
  // case we don't want to do that because negative numbers were already
  // handled in the previous block.
  if (First != '-') {
    errno = 0;
    uint64_t UI = std::strtoull(S.data(), &End, 10);
    if (End == S.end() && errno != ERANGE) {
      Out = UI;
      return true;
    }
  }
  // If it's not an integer
  Out = std::strtod(S.data(), &End);
  return End == S.end() || parseError("Invalid JSON value (number?)");
}

bool Parser::parseString(std::string &Out) {
  // leading quote was already consumed.
  for (char C = next(); C != '"'; C = next()) {
    if (LLVM_UNLIKELY(P == End))
      return parseError("Unterminated string");
    if (LLVM_UNLIKELY((C & 0x1f) == C))
      return parseError("Control character in string");
    if (LLVM_LIKELY(C != '\\')) {
      Out.push_back(C);
      continue;
    }
    // Handle escape sequence.
    switch (C = next()) {
    case '"':
    case '\\':
    case '/':
      Out.push_back(C);
      break;
    case 'b':
      Out.push_back('\b');
      break;
    case 'f':
      Out.push_back('\f');
      break;
    case 'n':
      Out.push_back('\n');
      break;
    case 'r':
      Out.push_back('\r');
      break;
    case 't':
      Out.push_back('\t');
      break;
    case 'u':
      if (!parseUnicode(Out))
        return false;
      break;
    default:
      return parseError("Invalid escape sequence");
    }
  }
  return true;
}

static void encodeUtf8(uint32_t Rune, std::string &Out) {
  if (Rune < 0x80) {
    Out.push_back(Rune & 0x7F);
  } else if (Rune < 0x800) {
    uint8_t FirstByte = 0xC0 | ((Rune & 0x7C0) >> 6);
    uint8_t SecondByte = 0x80 | (Rune & 0x3F);
    Out.push_back(FirstByte);
    Out.push_back(SecondByte);
  } else if (Rune < 0x10000) {
    uint8_t FirstByte = 0xE0 | ((Rune & 0xF000) >> 12);
    uint8_t SecondByte = 0x80 | ((Rune & 0xFC0) >> 6);
    uint8_t ThirdByte = 0x80 | (Rune & 0x3F);
    Out.push_back(FirstByte);
    Out.push_back(SecondByte);
    Out.push_back(ThirdByte);
  } else if (Rune < 0x110000) {
    uint8_t FirstByte = 0xF0 | ((Rune & 0x1F0000) >> 18);
    uint8_t SecondByte = 0x80 | ((Rune & 0x3F000) >> 12);
    uint8_t ThirdByte = 0x80 | ((Rune & 0xFC0) >> 6);
    uint8_t FourthByte = 0x80 | (Rune & 0x3F);
    Out.push_back(FirstByte);
    Out.push_back(SecondByte);
    Out.push_back(ThirdByte);
    Out.push_back(FourthByte);
  } else {
    llvm_unreachable("Invalid codepoint");
  }
}

// Parse a UTF-16 \uNNNN escape sequence. "\u" has already been consumed.
// May parse several sequential escapes to ensure proper surrogate handling.
// We do not use ConvertUTF.h, it can't accept and replace unpaired surrogates.
// These are invalid Unicode but valid JSON (RFC 8259, section 8.2).
bool Parser::parseUnicode(std::string &Out) {
  // Invalid UTF is not a JSON error (RFC 8529§8.2). It gets replaced by U+FFFD.
  auto Invalid = [&] { Out.append(/* UTF-8 */ {'\xef', '\xbf', '\xbd'}); };
  // Decodes 4 hex digits from the stream into Out, returns false on error.
  auto Parse4Hex = [this](uint16_t &Out) -> bool {
    Out = 0;
    char Bytes[] = {next(), next(), next(), next()};
    for (unsigned char C : Bytes) {
      if (!std::isxdigit(C))
        return parseError("Invalid \\u escape sequence");
      Out <<= 4;
      Out |= (C > '9') ? (C & ~0x20) - 'A' + 10 : (C - '0');
    }
    return true;
  };
  uint16_t First; // UTF-16 code unit from the first \u escape.
  if (!Parse4Hex(First))
    return false;

  // We loop to allow proper surrogate-pair error handling.
  while (true) {
    // Case 1: the UTF-16 code unit is already a codepoint in the BMP.
    if (LLVM_LIKELY(First < 0xD800 || First >= 0xE000)) {
      encodeUtf8(First, Out);
      return true;
    }

    // Case 2: it's an (unpaired) trailing surrogate.
    if (LLVM_UNLIKELY(First >= 0xDC00)) {
      Invalid();
      return true;
    }

    // Case 3: it's a leading surrogate. We expect a trailing one next.
    // Case 3a: there's no trailing \u escape. Don't advance in the stream.
    if (LLVM_UNLIKELY(P + 2 > End || *P != '\\' || *(P + 1) != 'u')) {
      Invalid(); // Leading surrogate was unpaired.
      return true;
    }
    P += 2;
    uint16_t Second;
    if (!Parse4Hex(Second))
      return false;
    // Case 3b: there was another \u escape, but it wasn't a trailing surrogate.
    if (LLVM_UNLIKELY(Second < 0xDC00 || Second >= 0xE000)) {
      Invalid();      // Leading surrogate was unpaired.
      First = Second; // Second escape still needs to be processed.
      continue;
    }
    // Case 3c: a valid surrogate pair encoding an astral codepoint.
    encodeUtf8(0x10000 | ((First - 0xD800) << 10) | (Second - 0xDC00), Out);
    return true;
  }
}

bool Parser::parseError(const char *Msg) {
  int Line = 1;
  const char *StartOfLine = Start;
  for (const char *X = Start; X < P; ++X) {
    if (*X == 0x0A) {
      ++Line;
      StartOfLine = X + 1;
    }
  }
  Err = ParseError(Msg, Line, P - StartOfLine, P - Start);
  return false;
}

std::pair<std::optional<Value>, std::optional<ParseError>> parse(StringRef JSON) {
  Parser P(JSON);
  Value E = nullptr;
  if (P.checkUTF8())
    if (P.parseValue(E))
      if (P.assertEnd())
        return {std::move(E), std::nullopt};
  return {std::nullopt, P.takeError()};
}
// char ParseError::ID = 0;

/// Checks whether character \p C is valid ASCII (high bit is zero).
static inline bool isASCII(char C) { return static_cast<unsigned char>(C) <= 127; }

/// Checks whether all characters in S are ASCII.
static inline bool isASCII(llvm::StringRef S) {
  for (char C : S)
    if (LLVM_UNLIKELY(!isASCII(C)))
      return false;
  return true;
}

bool isUTF8(llvm::StringRef S, size_t *ErrOffset) {
  // Fast-path for ASCII, which is valid UTF-8.
  if (LLVM_LIKELY(isASCII(S)))
    return true;

  const UTF8 *Data = reinterpret_cast<const UTF8 *>(S.data()), *Rest = Data;
  if (LLVM_LIKELY(isLegalUTF8String(&Rest, Data + S.size())))
    return true;

  if (ErrOffset)
    *ErrOffset = Rest - Data;
  return false;
}

std::string fixUTF8(llvm::StringRef S) {
  // This isn't particularly efficient, but is only for error-recovery.
  std::vector<UTF32> Codepoints(S.size()); // 1 codepoint per byte suffices.
  const UTF8 *In8 = reinterpret_cast<const UTF8 *>(S.data());
  UTF32 *Out32 = Codepoints.data();
  ConvertUTF8toUTF32(&In8, In8 + S.size(), &Out32, Out32 + Codepoints.size(),
                     lenientConversion);
  Codepoints.resize(Out32 - Codepoints.data());
  std::string Res(4 * Codepoints.size(), 0); // 4 bytes per codepoint suffice
  const UTF32 *In32 = Codepoints.data();
  UTF8 *Out8 = reinterpret_cast<UTF8 *>(&Res[0]);
  ConvertUTF32toUTF8(&In32, In32 + Codepoints.size(), &Out8, Out8 + Res.size(),
                     strictConversion);
  Res.resize(reinterpret_cast<char *>(Out8) - Res.data());
  return Res;
}

enum class HexPrintStyle { Upper, Lower, PrefixUpper, PrefixLower };

/// hexdigit - Return the hexadecimal character for the
/// given number \p X (which should be less than 16).
static inline char hexdigit(unsigned X, bool LowerCase = false) {
  assert(X < 16);
  static const char LUT[] = "0123456789ABCDEF";
  const uint8_t Offset = LowerCase ? 32 : 0;
  return LUT[X] | Offset;
}

static void write_hex(std::ostream &S, uint64_t N, HexPrintStyle Style,
                     std::optional<size_t> Width) {
  const size_t kMaxWidth = 128u;

  size_t W = std::min(kMaxWidth, Width.value_or(0u));

  unsigned Nibbles = (llvm::bit_width(N) + 3) / 4;
  bool Prefix = (Style == HexPrintStyle::PrefixLower ||
                 Style == HexPrintStyle::PrefixUpper);
  bool Upper =
      (Style == HexPrintStyle::Upper || Style == HexPrintStyle::PrefixUpper);
  unsigned PrefixChars = Prefix ? 2 : 0;
  unsigned NumChars =
      std::max(static_cast<unsigned>(W), std::max(1u, Nibbles) + PrefixChars);

  char NumberBuffer[kMaxWidth];
  ::memset(NumberBuffer, '0', std::size(NumberBuffer));
  if (Prefix)
    NumberBuffer[1] = 'x';
  char *EndPtr = NumberBuffer + NumChars;
  char *CurPtr = EndPtr;
  while (N) {
    unsigned char x = static_cast<unsigned char>(N) % 16;
    *--CurPtr = hexdigit(x, !Upper);
    N /= 16;
  }

  S.write(NumberBuffer, NumChars);
}

static void quote(std::ostream &OS, llvm::StringRef S) {
  OS << '\"';
  for (unsigned char C : S) {
    if (C == 0x22 || C == 0x5C)
      OS << '\\';
    if (C >= 0x20) {
      OS << C;
      continue;
    }
    OS << '\\';
    switch (C) {
    // A few characters are common enough to make short escapes worthwhile.
    case '\t':
      OS << 't';
      break;
    case '\n':
      OS << 'n';
      break;
    case '\r':
      OS << 'r';
      break;
    default:
      OS << 'u';
      write_hex(OS, C, HexPrintStyle::Lower, 4);
      break;
    }
  }
  OS << '\"';
}

void llvm::json::OStream::value(const Value &V) {
  switch (V.kind()) {
  case Value::Null:
    valueBegin();
    OS << "null";
    return;
  case Value::Boolean:
    valueBegin();
    OS << (*V.getAsBoolean() ? "true" : "false");
    return;
  case Value::Number:
    valueBegin();
    if (V.Type == Value::T_Integer)
      OS << *V.getAsInteger();
    else if (V.Type == Value::T_UINT64)
      OS << *V.getAsUINT64();
    else {
      char Buffer[64];
      snprintf(Buffer, sizeof(Buffer), "%.*g", std::numeric_limits<double>::max_digits10,
                   *V.getAsNumber());
      OS << Buffer;
    }
    return;
  case Value::String:
    valueBegin();
    quote(OS, *V.getAsString());
    return;
  case Value::Array:
    return array([&] {
      for (const Value &E : *V.getAsArray())
        value(E);
    });
  case Value::Object:
    return object([&] {
      for (const Object::value_type *E : sortedElements(*V.getAsObject()))
        attribute(E->first, E->second);
    });
  }
}

void llvm::json::OStream::valueBegin() {
  assert(Stack.back().Ctx != Object && "Only attributes allowed here");
  if (Stack.back().HasValue) {
    assert(Stack.back().Ctx != Singleton && "Only one value allowed here");
    OS << ',';
  }
  if (Stack.back().Ctx == Array)
    newline();
  flushComment();
  Stack.back().HasValue = true;
}

void OStream::comment(llvm::StringRef Comment) {
  assert(PendingComment.empty() && "Only one comment per value!");
  PendingComment = Comment;
}

void OStream::flushComment() {
  if (PendingComment.empty())
    return;
  OS << (IndentSize ? "/* " : "/*");
  // Be sure not to accidentally emit "*/". Transform to "* /".
  while (!PendingComment.empty()) {
    auto Pos = PendingComment.find("*/");
    if (Pos == StringRef::npos) {
      OS << PendingComment;
      PendingComment = "";
    } else {
      OS << PendingComment.substr(0, Pos) << "* /";
      PendingComment = PendingComment.substr(Pos + 2);
    }
  }
  OS << (IndentSize ? " */" : "*/");
  // Comments are on their own line unless attached to an attribute value.
  if (Stack.size() > 1 && Stack.back().Ctx == Singleton) {
    if (IndentSize)
      OS << ' ';
  } else {
    newline();
  }
}

template <char C>
static std::ostream &write_char(std::ostream &OS) {
  return OS << C;
}

template <char C>
static std::ostream &write_padding(std::ostream &OS, unsigned NumChars) {
  static const char Chars[] = {C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C,
                               C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C,
                               C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C,
                               C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C,
                               C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, C};

  // Usually the indentation is small, handle it with a fastpath.
  if (NumChars < std::size(Chars))
    return OS.write(Chars, NumChars);

  while (NumChars) {
    unsigned NumToWrite = std::min(NumChars, (unsigned)std::size(Chars) - 1);
    OS.write(Chars, NumToWrite);
    NumChars -= NumToWrite;
  }
  return OS;
}

/// indent - Insert 'NumSpaces' spaces.
std::ostream &write_indent(std::ostream &OS, unsigned NumSpaces) {
  return write_padding<' '>(OS, NumSpaces);
}

void llvm::json::OStream::newline() {
  if (IndentSize) {
    write_char<'\n'>(OS);
    write_indent(OS, Indent);
  }
}

void llvm::json::OStream::arrayBegin() {
  valueBegin();
  Stack.emplace_back();
  Stack.back().Ctx = Array;
  Indent += IndentSize;
  OS << '[';
}

void llvm::json::OStream::arrayEnd() {
  assert(Stack.back().Ctx == Array);
  Indent -= IndentSize;
  if (Stack.back().HasValue)
    newline();
  OS << ']';
  assert(PendingComment.empty());
  Stack.pop_back();
  assert(!Stack.empty());
}

void llvm::json::OStream::objectBegin() {
  valueBegin();
  Stack.emplace_back();
  Stack.back().Ctx = Object;
  Indent += IndentSize;
  OS << '{';
}

void llvm::json::OStream::objectEnd() {
  assert(Stack.back().Ctx == Object);
  Indent -= IndentSize;
  if (Stack.back().HasValue)
    newline();
  OS << '}';
  assert(PendingComment.empty());
  Stack.pop_back();
  assert(!Stack.empty());
}

void llvm::json::OStream::attributeBegin(llvm::StringRef Key) {
  assert(Stack.back().Ctx == Object);
  if (Stack.back().HasValue)
    OS << ',';
  newline();
  flushComment();
  Stack.back().HasValue = true;
  Stack.emplace_back();
  Stack.back().Ctx = Singleton;
  if (LLVM_LIKELY(isUTF8(Key))) {
    quote(OS, Key);
  } else {
    assert(false && "Invalid UTF-8 in attribute key");
    quote(OS, fixUTF8(Key));
  }
  write_char<':'>(OS);
  if (IndentSize)
    write_char<' '>(OS);
}

void llvm::json::OStream::attributeEnd() {
  assert(Stack.back().Ctx == Singleton);
  assert(Stack.back().HasValue && "Attribute must have a value");
  assert(PendingComment.empty());
  Stack.pop_back();
  assert(Stack.back().Ctx == Object);
}

std::ostream &llvm::json::OStream::rawValueBegin() {
  valueBegin();
  Stack.emplace_back();
  Stack.back().Ctx = RawValue;
  return OS;
}

void llvm::json::OStream::rawValueEnd() {
  assert(Stack.back().Ctx == RawValue);
  Stack.pop_back();
}

} // namespace json
} // namespace llvm

namespace llvm {
namespace json {
void format(
    const llvm::json::Value &E, std::ostream &OS, int IndentAmount) {
  // unsigned IndentAmount = 0;
  // if (!Options.empty() && Options.getAsInteger(/*Radix=*/10, IndentAmount))
  //   llvm_unreachable("json::Value format options should be an integer");
  json::OStream(OS, IndentAmount).value(E);
}
}
}
