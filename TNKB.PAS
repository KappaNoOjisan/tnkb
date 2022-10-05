{    TNKB                                                                }
{                                                                        }
{             Copyright (c) 1993,2017    K.Watanuki                      }


program TNKB(SourceTextFile,ObjectTextFile);

const
      tmax  = 100;  { Size of ID-table.         }
      lmax  = 200;  { Size of Source lines.     }
      dmax  =   5;  { Maximam value of digits.  }
      nrw   =  31;  { Number of reserved Words. }
      namel =   8;  { Length of name.           }
      linel =  80;  { Length of line.           }

type
  TErr = (
      erSN_ERR,
      erRP_EXP,
      erLP_EXP,
      erCM_EXP,
      erNX_MIS,
      erFR_MIS,
      erGS_MIS,
      erRT_MIS,
      erDM_MIS,
      erBD_XPR,
      erUD_LNO,
      erRS_MIS,
      erLN_MIS,
      erLT_OVR,
      erDP_IDN,
      erND_OVR
  );

  FErr = (
      ftID_OVR,
      ftDP_LIN,
      ftLN_MIS,
      ftRG_OVR
  );

const

      { Error message. }
      ErrMsg : Array [TErr] of String[19]
               =('Syntax error.      ',      { 00 }
                 '"(" expected.      ',      { 01 }
                 '")" expected.      ',      { 02 }
                 '"," expected.      ',      { 03 }
                 'NEXT is missing.   ',      { 04 }
                 'FOR  is missing.   ',      { 05 }
                 'GOSUB is missing.  ',      { 06 }
                 'RETURN is missing. ',      { 07 }
                 'DIM is missing.    ',      { 08 }
                 'Bad Expression.    ',      { 09 }
                 'Undefined Line-No. ',      { 10 }
                 'RESTORE is missing.',      { 11 }
                 'Line-No is missing.',      { 12 }
                 'Literal data over. ',      { 13 }
                 'Duplicate Identifer',      { 14 }
                 'Number Digits over.'       { 15 }
                );

      { Fatal Error message }
      FtlMsg : Array [FErr] of String[19]
               =(
                 'Too many ID define.',      { 00 }
                 'Duplicate line.    ',      { 01 }
                 'Line is missing.   ',      { 02 }
                 'Register overflow. '       { 03 }
                );
type
      FileName = String[14];

      SymbolKind =(

                   { Special Symbol }
                   EndofLine,  EndofFile,  BadSymbol,
                   Literal, Identifier, Letters,

                   { Alithmetic operator }
                   LeftParen, RightParen,  Asterisk,
                   Plus,      Minus,       Slant,

                   { Delimiter }
                   Colon,   Semicolon, Comma,
                   Sharp,   Ampersant,

                   { Relational operator }
                   SyLT,  SyLE, SyNE, SyEQ, SyGE, SyGT,

                   { Logical Arithmetic operator }
                   SyAND, syOR, syEOR,

                   { Reserved Words }
                   SyBEEP,   SyCLEAR,  SyCLS,    SyCURSOR, SyDATA,
                   SyDIM,    SyEND,    SyFOR,    SyGCURSOR,SyGOSUB,
                   SyGOTO,   SyGPRINT, SyIF,     SyINPUT,  SyLET,
                   SyNEXT,   SyPRESET, SyPRINT,  SyPSET,   SyREAD,
                   SyREM,    SyRESTORE,SyRETURN, SySTEP,   SyTO,
                   SyTHEN,   SyUSING,  SyWAIT,   SyINLINE, SyON
      );


      SymbolSet  = Set of SymbolKind;

      IdName     = String[Namel];   { Symbol name         }
      Card       = String[Linel];   { Assemble card       }

      typeKind   = (Intt,Notype);   { Notype is Error }

      MopKind    = (Immed, Index, Other);
      Mopt       = record
                     case Mopk: MopKind of
                       Immed: (NImm : Integer);
                       Index: (XBase: Boolean;
                               XStr : Boolean;
                               XInd : Integer);
                       Other: (Dummy: Integer)
                     end;

      ObjectKind =(oConstant, oVariable,
                   oFunction, oStatement);

      AtKind     =(Cons,Vari,Expr);
      Attribute  = record
                     Attype: typeKind;
                     case atk: AtKind of
                       Cons: (AtValue: Integer);
                       Vari: (AtAddr : Integer;
                              AtBase : Boolean;
                              AtStr  : Boolean)
                     end;

      Fort       = record
                     Initvalue : Mopt;
                     stepvalue : Mopt;
                     lastvalue : Mopt;
                     loopline  : Integer
                   end;

      Errt       = record
                     cnt        : Byte; { Line count }
                     pos        : Byte; { Column     }
                     erno       : TErr; { Error No   }
                   end;
var

  SourceTextFile, ObjectTextFile : Text;
  SourceFileName, ObjectFileName : FileName;

  G       : FileName;
  Filefail: Boolean;

  InCount : 0..lmax;
  cc,ll   : 0..linel;

  ch      : char;
  buff    : String[255];

  Symbol  : SymbolKind;

  SySc    : Array [char]   of SymbolKind; { Lexical charactor }
  SyRw    : Array [1..nrw] of SymbolKind; { Reserved Word }

  Hord    : Array [char]   of Byte;  { Hex->dec order }

  StatementHeader : SymbolSet;
  FunctionHeader  : SymbolSet;
  FactorHeader    : SymbolSet;


  { For Lexical check. }

  Id      : IdName; { Identifier Name }
  Strings : Card;
  IdStr   : Card;
  IdValue : Integer;

  Rw      : Array [0..nrw]  of IdName;  { <RESERVED Word> }

  t       : 0..tmax; { ID-TABLE ENTRY. }
  k       : Integer;


  NewAddr : Integer;

  Idtable : Array [0..tmax]of
            record
              Name   : IdName;
              Idtype : typeKind;
              Prev   : 0..tmax;
              case Object_ : ObjectKind of
                oConstant : ( Idvalue  : Integer   );
                oVariable : ( Idaddr   : Byte;
                              Based    : Boolean;
                              IsString : Boolean   );
                oFunction : ( IdNumber : Byte;     );
                oStatement: ( pstate   : 0.. tmax  );
              end;

  TopId,
  LastId  : 0..Tmax;

  Ltable  : Array [0..lmax] of Integer;    { Line table }
  Lnum    : 0..lmax;

  Rtable  : Array [0..lmax] of Integer;    { Reserve line-table }
  Rnum    : 0..lmax;

  ForTable: Array [0..lmax] of fort;       { For     line-table }
  Fnum    : 0..Lmax;
  ForLine : Integer;

  Errtable: Array [0..lmax] of errt;       { Error information  }
  i,Enum  : 0..lmax;

  CurLine : Integer;   { Current line-no   }
  Braline : Integer;   { Target Expression }

  ifLine  : Integer;   { Target for IF statement   }

  SourceTextLine: Card;     { One card from source file }
  TnkLabel: Card;      { Label                     }

  ErrPos  : 0..linel;  { Error detected position.  }

  ErrorDetect: Boolean;

  Fsys    : SymbolSet;


  Isfin   : Boolean;   { Endstatement flag }

{ Display Error message. }
{                        }
procedure Error(n : TErr);
  begin
    ErrorDetect := true;
    if ErrPos = 0 then
    begin
      if InCount >1
        then InCount := InCount -1
    end;
    if cc > ErrPos + 2 then { Display Error-position. }
    begin
      Write(' ' : cc-ErrPos-1, '^', ord(n):2);
      ErrPos := cc
    end
    else
      WriteLn('^', ord(n):2);
    enum := enum + 1;
    with Errtable[enum] do
    begin
      cnt  := InCount;
      pos  := ErrPos;
      erno := n
    end
  end;

procedure Fatal(n: Integer);
begin
  WriteLn;
  WriteLn('Fatal error.',n:4);
  Halt
end ; { Fatal }


{  GetSymbol                      }
{  Symbol: SymbolSet from source  }
{                                 }
procedure GetSymbol;
  label 1;
  var   i,j,k: Integer;

  {  GetNextCh       }
  procedure GetNextCh;

    function IsFirstLine : Boolean;
    begin
      IsFirstLine := (cc=0) and (ll=0);
    end;

    procedure GetNewLine;
    begin
      Read(SourceTextFile,SourceTextLine);
      WriteLn('     ',SourceTextLine);
      cc := 0;
      ll := Length(SourceTextLine);
    end;

    function DetectEOL: Boolean;
    begin
      if EoLn(SourceTextFile) then
      begin
        ch := ^A;
        ReadLn(SourceTextFile);
        DetectEOL := True;
        Exit;
      end;
      DetectEOL := False
    end;

    function DetectEOF: Boolean;
    begin
      if Eof(SourceTextFile) then
      begin
        ch := ^Z;
        DetectEOF := True;
        Exit;
      end;
      DetectEOF := False;
    end;

  begin

    if cc=ll then begin
      if DetectEOF then Exit;
      if DetectEOL then Exit;
      GetNewLine;
    end else begin
      { Buffered };
    end;

    cc := cc + 1;
    ch := SourceTextLine[cc];

  end; { Get next ch }


  begin
 1:
    while ch = ' ' do
      GetNextCh;

    case Upcase(ch) of
     '0'..'9': { Literal }
        begin
          Symbol  := Literal;
          IdValue := 0;
          IdStr   := '';
          k := 0;
          repeat
            IdValue := IdValue * 10 + ord(ch) - ord('0');
            IdStr   := IdStr + Ch;
            k := k + 1;
            GetNextCh
          until Not(ch in ['0'..'9']);
          if k > dmax then
          begin
            Error(erND_OVR);
            IdValue := 0;
            k := 0
          end
        end;

     'A'..'Z': { Identifier }
        begin
          Id := '        ';
          k  := 0;
          Ch := Upcase(ch);
          repeat
            if k < Namel then
            begin
              k := k +1;
              Id[k] := ch
            end;
            GetNextCh;
            Ch := Upcase(ch)
          until Not( ch in ['0'..'9', 'A'..'Z'] );
          if Ch = '$'
            then
            if k < Namel
              then begin
                k := k +1; Id[k] := ch;
                GetNextCh
              end;
          if ch = '('
            then
            if k < Namel
              then begin
                k := k +1; Id[k] := ch;
                GetNextCh
              end;
          i := 1;
          j := Nrw;
          repeat                   { Search Reserved Word }
            k := (i+j) div 2;
            if Id <= Rw[k] then j:= k-1;
            if Id >= Rw[k] then i:= k+1;
          until i > j;
          if i - 1 > j
            then Symbol := SyRw[k]     { Reserved Word }
            else Symbol := Identifier;
          if Symbol = SyREM
            then begin
              Strings := '';
              while Ch <> ^A
                do begin
                  GetNextCh;
                  Strings := Strings + Ch
                end
            end
        end;

     '!' :
        begin
          Symbol := SyInline;
          Strings := '';
          GetNextCh;
          repeat
            Strings := Strings + ch;
            GetNextCh
          until Not(Ch in['0'..'9','A'..'F']);
        end;

     '(',  ')',  '*',
     '/',  '+',  '#',
     ',',  '-',  '.',
     ';',  '=',  ':':
        begin
          Symbol := SySc[ch];
          GetNextCh
        end;

     '<':
        begin { Relational operator. }
          GetNextCh;
          if ch = '=' then
          begin
            Symbol := SyLE;
            GetNextCh
          end else if ch = '>'
            then begin Symbol := SyNE ; GetNextCh end
            else Symbol:= SyLT
        end;

     '>':
        begin
          GetNextCh;
          if ch = '=' then
          begin
            Symbol:= SyGE;
            GetNextCh
          end
          else
            Symbol:= SyGT
        end;

     '"':
        begin { Letters.}
          Strings := '';
          GetNextCh;
          while ch <> '"' do
          begin
            Strings := Strings + ch;
            GetNextCh
          end;
          Symbol:= Letters;
          GetNextCh
        end;

     '&':
        begin { Hexadecimal number. }
          GetNextCh;
          if Not(ch in ['0'..'9','A'..'F']) then
            Symbol:= Ampersant
          else begin
            Symbol  := Literal;
            IdValue := 0;
            k:= 0;
            repeat
              IdValue := IdValue * 16 + Hord[ch];
              k := k + 1;
              GetNextCh
            until Not(ch in ['0'..'9','A'..'F']);
            if k > dmax then
            begin
              Error(erSN_ERR);
              IdValue := 0;
              k    := 0
            end
          end
        end;

     '%',  '?',  '@',
     '[',  '\',  ']',
     '^',  '|',  '~':
        begin
          Error(erSN_ERR);
          GetNextCh;
          Goto 1
        end;

     ^Z : Symbol := EndofFile;

     ^A : begin
            Symbol := EndofLine;
            GetNextCh;
          end;

     else
          begin
            Symbol:= BadSymbol;
            GetNextCh;
          end;

    end; { CASE }

  end; { Get Symbol }


{  Id-table handring routine    }

procedure Enter(x: IdName; y: ObjectKind);
  label 1;
  var k: 0..tmax;

  begin
    if t >= tmax
      then fatal(101);
    k := LastId;
    while k <> TopId do
      begin
        if x = idtable[k].name
          then begin
            Error(erDP_IDN);  { Duplicate defInition. }
            Goto 1
          end ;
        k := idtable[k].prev
      end;
    t := t+1;           { X is a newcommer. }
    with idtable[t] do
      begin
        name    := x;
        idtype  := intt;
        prev    := LastId;
        Object_ := y
      end;
    LastId := t;
1:
  end; { Enter }


procedure EnterVariable;
  begin
    Enter(id,oVariable);
    with Idtable[t] do
      begin
        idaddr   := $26 + NewAddr;
        NewAddr  := NewAddr +1;
        based    := ( pos('(',id) <> 0 );
        isString := ( pos('$',id) <> 0 )
      end;
    if NewAddr > 26
      then fatal(103);
    GetSymbol
  end; { Enter Variable }


procedure EnterFunctionId;
  var num : Byte;

  procedure Enter(ent_name: IdName);
    begin
      t := t+1;
      with idtable[t] do begin
        name     := ent_name;
        idtype   := intt;
        Object_  := ofunction;
        IdNumber := num;
        num  := num + 1;
        prev := t-1
      end
    end;

  begin { Enter function id. }
    num := 0;
    Enter('ASC     ');
    Enter('CHR$    ');
    Enter('INKEY$  ');
    Enter('POINT(  ');
    Enter('RND     ');
    Enter('SQRT    ')
  end; { Enter function id. }


function Loc(x: IdName) : Integer;
  label 1;
  var   j: 0..tmax;
  begin
    j := LastId;
    while j <> TopId do
      begin
        if idtable[j].name = x
          then begin
            loc := j;
            Goto 1
          end;
        j := idtable[j].prev
      end;
    loc := 0;
1:
  end; { Loc }


procedure Enterlineno(lineno : Integer);
  label 1;
  var   k: 0..lmax;
  begin
    if lnum >= lmax
      then fatal(101);
    For k := 0 to lnum do
      begin
        if lineno <= ltable[k]
          then begin
            Error(erSN_ERR);
            Goto 1
          end;
      end;
    lnum := lnum+1;
    Ltable[lnum] := lineno;
    CurLine      := lineno;
1:
  end; { Enter line no. }

procedure Reservation(lineno: Integer);
  label 1;
  var   k: 0..lmax;
  begin
    For k := 0 to rnum do
      begin
        if lineno = rtable[k]
          then Goto 1;
      end;
    rtable[rnum] := lineno;
    rnum := rnum +1;
    if rnum > lmax
      then fatal(101);
1:
  end;


function Loclineno(lineno: Integer) : Integer;
  label 1;
  var   j: 0..lmax;
  begin
    for j := 0 to lnum do
      begin
        if ltable[j] = lineno
          then begin
            Loclineno := j;
            Goto 1
          end;
      end;
    Loclineno := 0;
1:
  end; { Location of line no }


procedure Enterfor(Initv,stepv,lastv:Mopt);
  begin
    with ForTable[Fnum] do
      begin
        Initvalue := Initv;
        stepvalue := stepv;
        lastvalue := lastv;
        loopline  := ForLine
      end;
    Fnum     := Fnum + 1;
    ForLine := ForLine + 1
  end; { Enter for. }


{   Auxiliary routines for code generation.    }

procedure PutLabel(CR: Boolean; C: Char; Var LineNo: Integer);
  var LabelStr : IdName;
      i        : Byte;
  begin
    Str(LineNo,LabelStr);
    LabelStr := C + LabelStr + ':';
    if Length(LabelStr) < 8
      then
      For i := 0 to 8-Length(LabelStr)
        do LabelStr := LabelStr + ' ';
    if CR
      then WriteLn(ObjectTextFile,LabelStr,' EQU   *')
      else TnkLabel := LabelStr + ' '
  end;

procedure PutTnkLabel;
  begin
    if TnkLabel[1] <> ' '
      then begin
        Write(ObjectTextFile,TnkLabel);
        TnkLabel := ' ';
      end
      else Write(ObjectTextFile,'         ');
  end;                    {  1.......9  }

procedure Scas1(code:Card);
  begin
    PutTnkLabel;
    WriteLn(ObjectTextFile,code)
  end;


procedure ScASM(code:IdName; Operand:Integer);
  begin
    PutTnkLabel;
    WriteLn(ObjectTextFile,code,operand)
  end;

procedure Lia(Lit:Integer);
  begin
    PutTnkLabel;
    WriteLn(ObjectTextFile,'LIA   ',lit)
  end;

procedure Exab;
  begin
    Scas1('EXAB')
  end;

procedure Exam;
  begin
    Scas1('EXAM')
  end;

procedure Adm;
  begin
    Scas1('ADM')
  end;

procedure Anma;
  begin
    Scas1('ANMA')
  end;

procedure Orma;
  begin
    Scas1('ORMA')
  end;

procedure Sbm;
  begin
    Scas1('SBM')
  end;

procedure Lp(lit: Integer);
  begin
    ScASM('LP    ',lit)
  end;

procedure DefB(lit: Integer);
  begin
    ScASM('DB    ',lit)
  end;

procedure DefH(Str: Card);
  begin
    PutTnkLabel;
    WriteLn(ObjectTextFile,'DH    ','"',Strings,'"')
  end;

procedure DefM(Slit: Card );
  begin
    PutTnkLabel;
    WriteLn(ObjectTextFile,'DM    ','"',Slit,'"')
  end;

procedure Call(Slit: Card );
  begin
    PutTnkLabel;
    WriteLn(ObjectTextFile,'CALL  ',Slit)
  end;

procedure AtToMop(Var x:Attribute; Var y:Mopt);
  begin
    with x,y do
    case atk of
      Cons: begin
              Mopk  := Immed;
              Nimm  := atvalue
            end;
      Vari: begin
              Mopk  := Index;
              XInd  := Ataddr;
              XBase := Atbase;
              XStr  := AtStr;
            end;
      Expr: Mopk := other
    end
  end;   { Attribute to operand }


procedure Skip(fsys: SymbolSet);
  begin
    while Not(Symbol in fsys+ [endofline])
      do GetSymbol;
  end; { skip }


{  STATEMENT compile routine.    }
procedure Statement;

  var Ntemp : Integer;
      a     : Attribute;

  procedure Push;
    begin
      if Ntemp = 0
        then Ntemp := 1
        else begin
          Ntemp := Ntemp + 1;
          ScAs1('Push')
        end
    end;

  procedure pop;
    begin
      Ntemp := Ntemp - 1
    end;

  procedure Lea(var y:Mopt);
    begin
      with y do
        if Mopk = index
          then begin
            if Not(xbase)
              then lp(xind)
          end
    end;

  procedure Lda(var y:Mopt);
    begin
      with y do
        case Mopk of
          Immed: if nimm = 0
                   then Scas1('CLRA')
                   else Lia(nimm);
          Index: begin
                   Lea(y);
                   if xbase
                     then begin
                       Ntemp := Ntemp -1;
                       if Ntemp = 1
                         then Scas1('POP')
                     end
                     else Scas1('LDM')
                 end
        end
    end;

  procedure Ldb(var y:Mopt);
    begin
      with y do
        case Mopk of
          immed: ScASM('LIB   ',nimm);
          index: begin
                   Exab;
                   Lda(y);
                   Exab;
                 end
        end
    end;


  {             <Expression> process.              }

  procedure Expression(var X: Attribute; Fsys: SymbolSet);
    var op     : SymbolKind;
        y      : Attribute;
        flgexp : Boolean;
        Mop1,
        Mop2   : Mopt;

    {       <SIMPLE Expression> process.     }

    procedure SimpleExpression(var x: Attribute; fsys: SymbolSet);
      var op         : SymbolKind;
          y          : Attribute;

      procedure FunctionCall(IdNumber: Byte);
        var x,y       : Attribute;
            Mop1,Mop2 : Mopt;
        begin
          case IdNumber of
            0: begin  { Asc    }
                 GetSymbol
               end;

            1: begin  { Chr$   }
                 GetSymbol
               end;

            2: begin  { Inkey$ }
                 Call('INKEY');
               end;

            3: begin  { Point  }
                 Expression(x,fsys);
                 if x.atk = Expr
                   then ScAs1('PUSH');
                 if Symbol<> Comma
                   then Error(erSN_ERR)
                   else GetSymbol;
                 Expression(y,fsys);
                 AtToMop(x,Mop1);
                 AtToMop(y,Mop2);
                 case x.atk of
                   Cons: case y.atk of
                           Cons,
                           Vari: begin
                                   Lda(Mop1);
                                   Ldb(Mop2)
                                 end;
                           Expr: begin
                                   Ldb(Mop1);
                                   Exab
                                 end
                         end;
                   Vari: case y.atk of
                           Cons: begin
                                   Lda(Mop1);
                                   Ldb(Mop2)
                                 end;
                           Vari: begin
                                   Lda(Mop2);
                                   Exab;
                                   Lda(Mop1)
                                 end;
                           Expr: Ldb(Mop1)
                         end;
                   Expr: case y.atk of
                           Cons,
                           Vari: Ldb(Mop2);
                           Expr: begin
                                   Exab;
                                   Scas1('POP');
                                   Exab
                                 end
                         end
                 end;
                 if Symbol<> RightParen
                   then Error(erSN_ERR)
                   else GetSymbol;
                 Call('POINT')
               end;

            4: begin  { Rnd    }
                 Expression(x,fsys);
                 AtToMop(x,Mop1);
                 case x.atk of
                   Cons,
                   Vari: Lda(Mop1);
                   Expr:
                 end;
                 Call('RND');
               end;

            5: begin  { Sqrt   }
                 Expression(x,fsys);
                 AtToMop(x,Mop1);
                 case x.atk of
                   Cons,
                   Vari: Lda(Mop1);
                   Expr:
                 end;
                 Call('SQRT')
               end;
          end
        end;

      {    <TERM> process.   }

      procedure Term(var x: Attribute; fsys:SymbolSet);

        var op   : SymbolKind;
            y    : Attribute;
            Mop1,
            Mop2 : Mopt;
            tmp  : Integer;  { Temporaly buffer for Asterisk. }
            tomul: Boolean;  { Do I have to Asterisk?         }

        {  <FACTOR> := <INT_LITERAL>|<Identifier>| ( <ExprESSION> )  }

        procedure Factor(var x: Attribute; fsys: SymbolSet);

          var i           : 0..tmax;
              z           : Attribute;
              Mop1,Mop3   : Mopt;
              ntsave      : Integer;

          begin  { Factor }
            x.attype := Notype;
            x.atstr  := False;
            if Not(Symbol in FactorHeader)
              then begin
                Error(erSN_ERR);
                Skip(fsys + FactorHeader);
              end
            else
              case Symbol of
                Literal:
                  begin
                    with x do begin
                      attype  := intt;
                      atk     := Cons;
                      atvalue := IdValue;
                    end;
                    GetSymbol
                  end;
                Letters:
                  begin
                    with x do begin
                      attype  := intt;
                      atk     := Cons;
                      atvalue := ord(Strings[1])
                    end;
                    GetSymbol
                  end;
                Identifier:
                  begin
                    i := loc(Id);
                    if i = 0
                      then begin
                        EnterVariable;
                        i := t;
                      end
                      else GetSymbol;
                    with IdTable[i],x do
                      case Object_ of
                        oConstant:
                          begin
                            attype  := Idtype;
                            atk     := Cons;
                            atvalue := IdValue
                          end;

                        oVariable:
                          begin
                            attype  := intt;
                            atk     := Vari;
                            ataddr  := idaddr;
                            atbase  := based;
                            if based       { Attach offSet address. }
                              then begin
                                Push;
                                Ntsave := Ntemp;
                                Ntemp  := 0;
                                SimpleExpression(z, fsys + [Rightparen]);
                                Ntemp  := Ntsave;
                                if Symbol= Rightparen { ')' found? }
                                  then GetSymbol
                                  else Error(erSN_ERR);
                                AtToMop(z,Mop3);
                                case z.atk of  { Add offSet address. }
                                  Cons:
                                    begin
                                      x.ataddr := x.ataddr + z.atvalue;
                                      x.atbase := false;
                                      Ntemp    := Ntemp -1
                                    end;
                                  Vari,
                                  Expr:
                                    begin
                                      if z.atk = Vari
                                        then Lda(Mop3);
                                      ScASM('ADIA  ',x.ataddr);
                                      Scas1('STP');
                                      Scas1('LDM')
                                    end
                                end
                              end
                          end;
                        ofunction:
                          begin
                            FunctionCall(IdNumber);
                            attype  := idtype;
                            atk     := Expr
                          end;
                        ostatement: Error(erSN_ERR)
                    end
                  end;
                LeftParen:
                  begin
                    GetSymbol;
                    Expression(x,fsys + [Rightparen]);
                    if Symbol= Rightparen
                      then GetSymbol
                      else Error(erSN_ERR)
                  end
              end
          end; { Factor }

        {  <TERM> := <FACTOR><MULTIPLISE_OPERATOR><FACTOR>      }

        begin
          Factor(x,fsys + [Asterisk, Slant, SyAND]);
          while Symbol in [Asterisk, Slant, SyAND] do
            begin
              Op := Symbol;
              GetSymbol;
              Factor(y,fsys+[Asterisk, Slant, SyAND]);
              if (x.attype = Notype) or (y.attype = Notype)
                then x.attype := Notype
                else begin
                  AtToMop(x,Mop1);
                  AtToMop(y,Mop2);
                  case Op of

                    Asterisk:
                      if (x.attype <> Intt) or (y.attype <> Intt)
                        then begin
                          Error(erSN_ERR);
                          x.attype := Notype
                        end
                        else begin
                          tomul := true;
                          case x.atk of
                            Cons:
                              case y.atk of
                                Cons: begin
                                        Push;
                                        Lia(x.atvalue * y.atvalue);
                                        tomul := false
                                      end;
                                Vari: if x.atvalue in [2,4,8,16]
                                        then begin
                                          tomul := false;
                                          Lda(Mop2);
                                          tmp := x.atvalue;
                                          while tmp <> 1
                                            do begin
                                              tmp := tmp div 2;
                                              Scas1('SL')
                                            end
                                        end
                                      else begin
                                        Push;
                                        Ldb(Mop1);
                                        Lda(Mop2)
                                      end;
                                Expr: Ldb(Mop1)
                              end;
                            Vari:
                              case y.atk of
                                Cons: if y.atvalue in [2,4,8,16]
                                        then begin
                                          tomul := false;
                                          Lda(Mop1);
                                          tmp := y.atvalue;
                                          while tmp <> 1
                                            do begin
                                              tmp := tmp div 2;
                                              Scas1('SL')
                                            end
                                        end
                                      else begin
                                        Push;
                                        Lda(Mop1);
                                        Ldb(Mop2)
                                      end;
                                Vari: begin
                                        if Not(y.atbase)
                                          then Push;
                                        Lda(Mop2);
                                        Exab;
                                        Lda(Mop1)
                                      end;
                                Expr: begin
                                        Exab;
                                        Lda(Mop2)
                                      end
                              end;
                            Expr:
                              case y.atk of
                                Cons: if y.atvalue in [2,4,8,16]
                                        then begin
                                          tomul := false;
                                          Lda(Mop1);
                                          tmp := y.atvalue;
                                          while tmp <> 1
                                            do begin
                                              tmp := tmp div 2;
                                              Scas1('SL')
                                            end
                                        end
                                        else Ldb(Mop2);
                                Vari: begin
                                        Exab;
                                        Lda(Mop2)
                                      end;
                                Expr: begin
                                        Exab;
                                        Scas1('POP');
                                        Pop
                                      end
                            end
                          end;  { CASE }
                          if tomul
                            then begin
                              Call('MULT');
                              Exab;
                            end;
                          x.atk := Expr
                        end;

                    Slant:
                      if (x.attype <> intt) or (y.attype <> intt)
                        then begin
                          Error(erSN_ERR);
                          x.attype := Notype
                        end
                        else begin
                          case x.atk of
                            Cons:
                              case y.atk of
                                Cons: begin
                                        Push;
                                        Lia(x.atvalue * y.atvalue);
                                      end;
                                Vari: begin
                                        if Not(y.atbase)
                                          then Push;
                                        Lda(Mop2);
                                        Ldb(Mop1);
                                        if Op = Slant
                                          then Exab
                                      end;
                                Expr: Ldb(Mop1)
                              end;
                            Vari:
                              case y.atk of
                                Cons,
                                Vari: begin
                                        if Not(y.atbase)
                                          then Push;
                                        Lda(Mop1);
                                        Ldb(Mop2)
                                      end;
                                Expr: begin
                                        Exab;
                                        Lda(Mop2)
                                      end
                              end;
                            Expr:
                              case y.atk of
                                Cons: Ldb(Mop2);
                                Vari: begin
                                        Exab;
                                        Lda(Mop2);
                                        Exab
                                      end;
                                Expr: begin
                                        Exab;
                                        Scas1('POP');
                                        pop
                                      end
                              end
                          end;
                          if (x.atk <> Cons) or (y.atk <> Cons)
                            then begin
                              Call('DIV');
                              Exab; { Update on 93.04.09 }
                            end;
                          x.atk := Expr
                        end;

                    SyAND:
                      if (x.attype <> intt) or (y.attype <> intt)
                        then begin
                          Error(erSN_ERR);
                          x.attype := Notype
                        end
                        else begin
                          case x.atk of
                            Cons:
                              case y.atk of
                                Cons: begin
                                        Push;
                                        Lia(x.atvalue and y.atvalue)
                                      end;
                                Vari: begin
                                        if Not(y.atbase)
                                          then Push;
                                        Lda(Mop2);
                                        ScASM('ANIA  ',x.atvalue)
                                      end;
                                Expr: ScASM('ANIA  ',x.atvalue)
                              end;
                            Vari:
                              case y.atk of
                                Cons: begin
                                        Push;
                                        Lda(Mop1);
                                        ScASM('ANIA  ',y.atvalue)
                                      end;
                                Vari: begin
                                        if Not(y.atbase)
                                          then Push;
                                        Lda(Mop1);
                                        Lea(Mop2);
                                        Exam;
                                        Anma;
                                        Exam
                                      end;
                                Expr: begin
                                        Lea(Mop1);
                                        Exam;
                                        Anma;
                                        Exam
                                      end
                              end;
                            Expr:
                              case y.atk of
                                Cons: ScASM('ANIA  ',y.atvalue);
                                Vari: begin
                                        Lea(Mop1);
                                        Exam;
                                        Anma;
                                        Exam
                                      end;
                                Expr: begin
                                        Exab;
                                        Pop;
                                        Scas1('POP');
                                        Lp(3);
                                        Anma;
                                        Exab
                                      end
                              end
                          end;
                          x.atk := Expr
                        end
                  end
                end;
            end
        end; { Term }

      { <SIMPLE Expression> := <TERM><ADD_OPERATOR><TERM> }
      begin
        Term(x,fsys+[Plus,Minus,syor]);
        while Symbol in [Plus,Minus,syor]
          do begin
          op := symbol;
          GetSymbol;
          Term(y,fsys+[Plus,Minus,syor]);
          if (x.attype <> Notype) and (y.attype <> Notype)
            then begin
              AtToMop(x,Mop1);
              AtToMop(y,Mop2);
              case op of
                Plus:
                  if (x.attype = intt) and (y.attype = intt)
                    then
                    case x.atk of
                      Cons:
                        begin
                          case y.atk of
                            Cons: lia(x.atvalue + y.atvalue);
                            Vari: begin
                                    if Not(y.atbase)
                                      then Push;
                                    Lda(Mop2);
                                    if x.atvalue = 1
                                      then Scas1('INCA')
                                      else ScASM('ADIA  ',x.atvalue)
                                  end;
                            Expr: begin
                                    Ldb(Mop2);
                                    Lp(3);
                                    Adm;
                                    Exab
                                  end
                          end
                        end;
                      Vari:
                        begin
                          case y.atk of
                            Cons: begin
                                    if Not(x.atbase)
                                      then Push;
                                    Lda(Mop1);
                                    if y.atvalue = 1
                                      then Scas1('INCA')
                                      else ScASM('ADIA  ',y.atvalue)
                                  end;
                            Vari: begin
                                    if Not(y.atbase) and Not(x.atbase)
                                      then Push;
                                    Lda(Mop2);
                                    Lea(Mop1);
                                    Exam;
                                    Adm;
                                    Exam
                                  end;
                            Expr: begin
                                    Lea(Mop1);
                                    Exam;
                                    Adm;
                                    Exam
                                  end
                          end
                        end;
                      Expr:
                        begin
                          case y.atk of
                            Cons: ScASM('ADIA  ',y.atvalue);
                            Vari: begin
                                    Lea(Mop2);
                                    Exam;
                                    Adm;
                                    Exam
                                  end;
                            Expr: begin
                                    Exab;
                                    Scas1('POP');
                                    Pop;
                                    Lp(3);
                                    Adm;
                                    Exab
                                  end
                          end
                        end
                    end
                    else begin
                      Error(erSN_ERR);
                      x.attype := Notype
                    end;
                Minus:
                  if (x.attype <> intt) or (y.attype <> intt)
                    then begin
                      Error(erSN_ERR);
                      x.Attype := Notype
                    end
                  else
                    case x.atk of
                      Cons:
                        begin
                          case y.atk of
                            Cons: begin
                                    Push;
                                    Lia(x.atvalue - y.atvalue)
                                  end;
                            Vari: begin
                                    if Not(y.atbase)
                                      then Push;
                                    Lda(Mop1);
                                    Lea(Mop2);
                                    Exam;
                                    Sbm;
                                    Exam
                                  end;
                            Expr: begin
                                    Ldb(Mop1);
                                    Lp(3);
                                    Scas1('SBM');
                                    Exab
                                  end
                          end
                        end;
                      Vari:
                        begin
                          case y.atk of
                            Cons: begin
                                    if Not(x.atbase)
                                      then Push;
                                    Lda(Mop1);
                                    if y.atvalue = 1
                                      then ScAs1('DECA')
                                      else ScASM('SBIA   ',y.atvalue)
                                  end;
                            Vari: begin
                                    if y.Atbase
                                      then begin
                                        Ldb(Mop1);
                                        Lp(3);
                                        Sbm;
                                        Exam
                                      end
                                      else begin
                                        Push;
                                        Lda(Mop1);
                                        Lea(Mop2);
                                        Exam;
                                        Sbm;
                                        Exam
                                      end
                                  end;
                            Expr: begin
                                    Lda(Mop1);
                                    Exab;
                                    Scas1('POP');
                                    Pop;
                                    Lp(3);
                                    Sbm;
                                    Exab
                                  end
                          end
                        end;
                      Expr:
                        begin
                          case y.atk of
                            Cons: ScASM('SBIA  ',y.atvalue);
                            Vari: begin
                                    Lp(y.ataddr);
                                    Exam;
                                    Sbm;
                                    Exam
                                  end;
                            Expr: begin
                                    Exab;
                                    Scas1('POP');
                                    Pop;
                                    Lp(3);
                                    Sbm;
                                    Exab
                                  end
                          end
                        end
                    end;

                SyOR:
                  if (x.attype <> intt) or (y.attype <> intt)
                    then begin
                      Error(erSN_ERR); x.attype := Notype
                    end
                    else
                      case x.atk of
                        Cons:
                          begin
                            case y.atk of
                              Cons: begin
                                      Push;
                                      Lia(x.atvalue or y.atvalue)
                                    end;
                              Vari: begin
                                      if Not(y.atbase)
                                        then Push;
                                      Lda(Mop2);
                                      ScASM('ORIA   ',x.atvalue)
                                    end;
                              Expr: ScASM('ORIA   ',x.atvalue)
                            end
                          end;
                        Vari:
                          begin
                            case y.atk of
                              Cons: begin
                                      if Not(y.atbase)
                                        then Push;
                                      Lda(Mop1);
                                      ScASM('ORIA   ',y.atvalue)
                                    end;
                              Vari: begin
                                      if Not(y.Atbase)
                                        then Push;
                                      Lda(Mop1);
                                      Lea(Mop2);
                                      Exam;
                                      Orma;
                                      Exam
                                    end;
                              Expr: begin
                                      Ldb(Mop1);
                                      Lp(3);
                                      Orma;
                                      Exam
                                    end
                            end
                          end;
                        Expr:
                          begin
                            case y.atk of
                              Cons: ScASM('ADIA  ',y.atvalue);
                              Vari: begin
                                      Lp(y.ataddr);
                                      Exam;
                                      Orma;
                                      Exam
                                    end;
                              Expr: begin
                                      Exab;
                                      Scas1('POP');
                                      Pop;
                                      Lp(3);
                                      Orma;
                                      Exab
                                    end
                            end
                          end
                      end
              end;
              x.atk := Expr
            end
            else x.attype := Notype
        end
    end; { Simple Expression }

  {  <ExprESSION> := <SIMPLE_ExprESSION><RELATIVE_OP><SIMPLE_ExprESSION>  }

  begin
    SimpleExpression(x, fsys + [SyLT, SyLE, SyNE, SyEQ, SyGT, SyGE]);
    if Symbol in [SyLT, SyLE, SyNE, SyEQ, SyGT, SyGE]
      then begin
        Op := symbol;
        GetSymbol;
        SimpleExpression(y,fsys);
        if (x.attype <> intt) or (y.attype <> intt)
          then begin
            Error(erSN_ERR);
            x.attype := Notype
          end
        else begin
          AtToMop(x,Mop1);
          AtToMop(y,Mop2);
  	  case x.atk of
            Cons: case y.atk of
                    Cons: begin
                            case Op of
                              SyEQ: Flgexp := (x.atvalue =  y.atvalue);
                              SyNE: Flgexp := (x.atvalue <> y.atvalue);
                              SyGE: Flgexp := (x.atvalue >= y.atvalue);
                              SyGT: Flgexp := (x.atvalue >  y.atvalue);
                              SyLE: Flgexp := (x.atvalue <= y.atvalue);
                              SyLT: Flgexp := (x.atvalue <  y.atvalue)
                            end;
                            if Flgexp
                              then Scas1('LIA    0FFH')
                              else Scas1('CLRA')
                          end;
                    Vari,
                    Expr: begin
                            if y.atk = Vari
                               then begin
                                 if Not(y.atbase)
                                   then Push;
                                 Lea(Mop2);
                                 ScASM('CPIM  ',x.atvalue)
                               end
                               else ScAsm('CPIA  ',x.atvalue);
                            if Op <> SyGE
                              then Scas1('CLRA')
                              else Scas1('LIA   0FFH');
                            case Op of
                              SyEQ: ScASM('JRNZP T',braline);
                              SyNE: ScASM('JRZP  T',braline);
                              SyGE: begin
                                      ScASM('JRNCP T',braline);
                                      ScASM('JRZP  T',braline)
                                    end;
                              SyGT: ScASM('JRCP  T',braline);
                              SyLE: ScASM('JRNCP T',braline);
                              SyLT: begin
                                      ScASM('JRCP  T',braline);
                                      ScASM('JRZP  T',braline)
                                    end
                            end;
                            if Op <> SyGE
                              then Scas1('DECA')
                              else Scas1('INCA');
                            PutLabel(False,'T',BraLine);
                            BraLine := BraLine +1
                          end;
                  end;
            Vari,
            Expr: begin
                    if x.atk = Vari
                      then begin
                        case y.atk of
                          Cons: begin
                                  Lea(Mop1);
                                  ScASM('CPIM  ',y.atvalue)
                                end;
                          Vari: begin
                                  if Not(y.Atbase)
                                    then Push;
                                  Lda(Mop2);
                                  Lea(Mop1);
                                  Scas1('CPMA')
                                end;
                          Expr: begin
                                  Lea(Mop1);
                                  Scas1('CPMA')
                                end
                        end
                      end
                      else { x.atk = Expr }
                        case y.atk of
                          Cons: begin
                                  ScASM('CPIA  ',y.atvalue)
                                end;
                          Vari: begin
                                  Lea(Mop2);
                                  Scas1('CPMA')
                                end;
                          Expr: begin
                                  Exab;
                                  Scas1('POP');
                                  Pop;
                                  Lp(3);
                                  Scas1('CPMA');
                                end
                        end;
                    if Op <> SyLE
                      then Scas1('CLRA')
                      else Scas1('LIA   0FFH');
                    case Op of
                      SyEQ: ScASM('JRNZP T',braline);
                      SyNE: ScASM('JRZP  T',braline);
                      SyGE: ScASM('JRNCP T',braline);
                      SyGT: begin
                              ScASM('JRCP  T',braline);
                              ScASM('JRZP  T',braline)
                            end;
                      SyLT: ScASM('JRCP  T',braline);
                      SyLE: begin
                              ScASM('JRNCP T',braline);
                              ScASM('JRZP  T',braline)
                            end
                    end;
                    if Op <> SyLE
                      then Scas1('DECA')
                      else Scas1('INCA');
                    Putlabel(False,'T',BraLine);
                    BraLine := BraLine +1
                  end;
          end; { case x.atk of  }
          x.atk := Expr
        end
      end
  end; { Expression }


{   STATEMENT has variety styles.     }
{  One of them is AssignStatement.    }

  procedure AssignStatement;
    label 1;
    var y,z     : Attribute;   { Base addr and Source value }
        i       : 0..tmax;
        Mop1,Mop2,Mop3 : Mopt;
    begin
      i := loc(id);
      if i <> 0
        then GetSymbol
      else begin
        EnterVariable;
        i := t
      end;
      { Check <Variable> }
      if idtable[i].Object_ <> oVariable
        then begin
          Error(erSN_ERR);
          skip(fsys);
          Goto 1
        end;
      with idtable[i],a do
        begin
          attype  := intt;
          atk     := Vari;
          ataddr  := idaddr;
          atbase  := based
        end;
      AtToMop(a,Mop1);
      if a.atbase
        then begin { Y is Attribute of base. }
          Ntemp := 0;
          Expression(y, fsys + [RightParen]);
          if Symbol<> RightParen
            then begin
              Error(erSN_ERR);
              Skip(fsys);
              Goto 1
            end;
          AtToMop(y,Mop2);
          case y.atk of
            Cons: lia(a.ataddr+y.atvalue);
            Vari: begin
                    Lda(Mop2);
                    ScASM('ADIA  ', a.atvalue)
                  end;
            Expr:
          end;
          GetSymbol;
          ScAs1('PUSH');
        end;  { if a.atbase }
      { Check <Equal> }
      if Symbol= SyEQ
        then GetSymbol
      else begin
        Error(erSN_ERR);
        skip(fsys+[Colon,endofline]);
        Goto 1
      end;
      Ntemp := 0;
      Expression(z,fsys);
      AtToMop(z,Mop3);
      case z.atk of
        Cons,
        Vari: Lda(Mop3);
        Expr:
      end;
      { Store value }
      if Not(a.atbase)
        then begin         { Simple Variable }
          Lea(Mop1);
          Exam
        end
        else begin
          Exab;            { Based  Variable }
          Scas1('POP');
          Scas1('STP');
          Exab;
          Exam
        end;
    1:
    end; { Assign statement }

  procedure BeepStatement;
    begin
      GetSymbol;
      case Symbol of
        Letters: if Strings <> ''
                  then begin
                    GetSymbol;
                    Call('BEEP');
                    DefM(Strings);
                    DefB($0D)
                  end;
        SyON:     begin
                    GetSymbol;
                    lp($1F);
                    Scas1('ORIM  0FFH')
                  end;
        else      begin
                    lp($1F);
                    Scas1('ANIM  0')
                  end
      end
    end;

  procedure ClearStatement;
    begin
      Call('CLEAR');
      GetSymbol
    end;

  procedure ClsStatement;
    begin
      GetSymbol;
      if Symbol<> Literal
        then Call('CLS')
        else begin
          GetSymbol;
          if IdValue > 4
            then Error(erSN_ERR);
          ScASM('LIB   ',IdValue);
          Call('CLSN')
        end
    end;

  procedure CursorStatement;
    label  1;
    var x,y       : Attribute;
        Mop1,Mop2 : Mopt;
    begin
      GetSymbol;
      Ntemp := 0;
      Expression(x,fsys);
      if x.atk = Expr
        then ScAs1('PUSH');
      if Symbol<> Comma
        then begin
          Error(erSN_ERR);
          Skip(fsys);
          Goto 1
        end;
      GetSymbol;
      Expression(y,fsys);
      AtToMop(x,Mop1);
      AtToMop(y,Mop2);
      case x.atk of
        Cons: case y.atk of
                Cons,
                Vari: begin
                        Lda(Mop1);
                        Ldb(Mop2)
                      end;
                Expr: begin
                        Ldb(Mop1);
                        Exab
                      end
              end;
        Vari: case y.atk of
                Cons: begin
                        Lda(Mop1);
                        Ldb(Mop2)
                      end;
                Vari: begin
                        Lda(Mop2);
                        Exab;
                        Lda(Mop1)
                      end;
                Expr: Ldb(Mop1)
              end;
        Expr: case y.atk of
                Cons,
                Vari: Ldb(Mop2);
                Expr: begin
                        Exab;
                        Scas1('POP');
                        Exab
                      end
              end;
      end;
      lp(22);
      ScASM('LIQ   ',2);
      Scas1('MVB');
   1:
    end; { Cursor statement }

  procedure DataStatement;
    var x : Attribute;
    begin
      GetSymbol;
      if Symbol<> Literal
        then Error(erSN_ERR)
        else begin
          DefB(IdValue);
          GetSymbol;
          while Symbol= Comma
            do begin
              GetSymbol;
              if Symbol= Literal
                then begin
                  DefB(IdValue);
                  GetSymbol
                end
                else Error(erSN_ERR)
            end
        end
    end;

  procedure DimStatement;
    label 1;
    begin
      repeat
        GetSymbol;
        if Symbol<> Identifier
          then begin
            Error(erSN_ERR);
            Skip(fsys);
            Goto 1
          end;
        if loc(id) <> 0
          then begin
            Error(erSN_ERR);    { Duplicate definition. }
            Skip(fsys);
            Goto 1
          end;
        GetSymbol;
        if Symbol<> Literal
          then begin
            Error(erSN_ERR);
            Skip(fsys);
            Goto 1
          end;
        EnterVariable;
        NewAddr := NewAddr + IdValue -1;
        if Symbol<> Rightparen
          then begin
            Error(erSN_ERR);
            Skip(fsys);
            Goto 1
          end;
        GetSymbol;
      until Symbol<> Comma;
  1:
    end;


  procedure EndStatement;
    begin
      Call('BYE');
      GetSymbol;
      Isfin := true
    end;

  procedure ForStatement;
    var f     : Attribute;
        i,s,l : Mopt;
    label 1;
    begin
      GetSymbol;
      Assignstatement;
      if Symbol<> SyTO
        then begin
          Error(erSN_ERR);
          Skip(fsys);
          Goto 1
        end;
      PutLabel(False,'N',ForLine);
      AtToMop(a,i);
      GetSymbol;
      Expression(f,fsys);
      AtToMop(f,l);
      if Symbol= SySTEP
        then begin
          GetSymbol;
          Expression(f,fsys);
          AtToMop(f,s)
        end
      else
        with s do begin
          Mopk    := immed;
          nimm    :=     1;
        end;
      Enterfor(i,s,l);
      case l.Mopk of
        Immed: begin
                 ScASM('CPIM  ',l.nimm)
               end;
        Index: begin
                 Ldb(i);
                 Lda(l);
                 lp(3);
                 Scas1('CPMA')
               end;
        Other: begin
                 Scas1('CPMA')
               end
      end;
      with ForTable[fnum-1] do
        begin
          ScASM('JRZP  Y',loopline);
          ScASM('JPNC  X',loopline);
          PutLabel(True,'Y',LoopLine);
        end;
  1:
    end;


  procedure GcursorStatement;
    label 1;
    var   x,y       : Attribute;
          Mop1,Mop2 : Mopt;
    begin
      GetSymbol;
      Ntemp := 0;
      Expression(x,fsys);
      if x.atk = Expr
        then ScAs1('PUSH');
      if Symbol<> Comma
        then begin
          Error(erSN_ERR);
          Skip(fsys);
          Goto 1
        end;
      GetSymbol;
      Expression(y,fsys);
      AtToMop(x,Mop1);
      AtToMop(y,Mop2);
      case x.atk of
        Cons: case y.atk of
                Cons,
                Vari: begin
                        Lda(Mop1);
                        Ldb(Mop2)
                      end;
                Expr: begin
                        Ldb(Mop1);
                        Exab
                      end
              end;
        Vari: case y.atk of
                Cons: begin
                        Lda(Mop1);
                        Ldb(Mop2)
                      end;
                Vari: begin
                        Lda(Mop2);
                        Exab;
                        Lda(Mop1)
                      end;
                Expr: Ldb(Mop1)
              end;
        Expr: case y.atk of
                Cons,
                Vari: Ldb(Mop2);
                Expr: begin
                        Exab;
                        Scas1('POP');
                        Exab
                      end
              end;
      end;
      Lp(24);
      ScASM('LIQ   ',2);
      Scas1('MVB');
      if Symbol<> RightParen
        then begin
          Error(erSN_ERR);
          Skip(fsys);
          Goto 1
        end;
      GetSymbol;
  1:
    end;

  procedure GosubStatement;
    begin
      GetSymbol;
      if Symbol<> Literal
        then Error(erSN_ERR);
      if Loclineno(IdValue) = 0
        then
        if IdValue < CurLine
          then Error(erSN_ERR)
          else Reservation(IdValue);
      ScASM('CALL  L',IdValue);
      GetSymbol
    end; { Gosub }


  procedure GotoStatement;
    begin
      GetSymbol;
      if Symbol<> Literal
        then Error(erSN_ERR);
      if Loclineno(IdValue) = 0
        then
        if IdValue < CurLine
          then Error(erSN_ERR) { Undefined Lineno. }
          else Reservation(IdValue);
      if IdValue = CurLine
        then ScASM('JRM   L',IdValue)
        else ScASM('JP    L',IdValue);
      GetSymbol
    end; { Goto }

  procedure GprintStatement;
    var x        : Attribute;
        TyFormat : Boolean;
        N        : Integer;
    begin
      TyFormat := false;
      GetSymbol;
      if Symbol= Sharp
        then begin
          GetSymbol;
          if Symbol <> Literal
            then Error(erSN_ERR)
            else begin
              TyFormat := True;
              N := IdValue
            end;
          GetSymbol
        end;
      if Symbol = Letters
        then begin
          if Strings = ''
            then Call('GPRINT1')
            else begin
              if TyFormat
                then begin
                  Lia(N);
                  Call('GPRINT2')
                end
                else Call('GPRINT3');
              DefB(Length(Strings)-1);
              DefH(Strings);
            end;
          GetSymbol
        end
        else begin
          if Symbol in FactorHeader
            then begin
              Expression(x,fsys);
              Exab;
              if TyFormat
                then begin
                  Lia(N);
                  Call('GPRINT4')
                end
                else Call('GPRINT5')
            end
            else Call('GPRINT1')
        end
    end; { Gprint }

  procedure ifStatement;
    var x:     Attribute;
        LblNo: Integer;
    begin
      LblNo  := ifLine;
      ifLine := ifLine+1;
      GetSymbol;
      Ntemp := 0;
      Expression(x,fsys + [SyLET,SyTHEN]);
      Scas1('SL');
      ScASM('JPNC  E',LblNo);
      case Symbol of
        SyLET:
          begin
            GetSymbol;
            Assignstatement;
            if Symbol <> EndofLine
              then repeat
                Statement
              until Symbol <> Colon
          end;
        SyTHEN:
          begin
            repeat
              Statement
            until Symbol <> Colon
          end;
        else
          Error(erSN_ERR)
      end;
      Putlabel(True,'E',LblNo);
      if Symbol <> EndofLine
        then GetSymbol;
    end;

  procedure PresetStatement;
    var x,y       : Attribute;
        Mop1,Mop2 : Mopt;
    begin
      GetSymbol;
      Expression(x,fsys);
      if x.atk = Expr
        then ScAs1('PUSH');
      if Symbol<> Comma
        then Error(erSN_ERR)
        else GetSymbol;
      Expression(y,fsys);
      AtToMop(x,Mop1);
      AtToMop(y,Mop2);
      case x.atk of
        Cons: case y.atk of
                Cons,
                Vari: begin
                        Lda(Mop1);
                        Ldb(Mop2)
                      end;
                Expr: begin
                        Ldb(Mop1);
                        Exab
                      end
              end;
        Vari: case y.atk of
                Cons: begin
                        Lda(Mop1);
                        Ldb(Mop2)
                      end;
                Vari: begin
                        Lda(Mop2);
                        Exab;
                        Lda(Mop1)
                      end;
                Expr: Ldb(Mop1)
              end;
        Expr: case y.atk of
                Cons,
                Vari: Ldb(Mop2);
                Expr: begin
                        Exab;
                        Scas1('POP');
                        Exab
                      end
              end;
      end;
      if Symbol<> RightParen
        then Error(erSN_ERR)
        else GetSymbol;
      Call('PRESET')
    end;

  procedure InputStatement;
    label   1;
    var     s   : Attribute;
            Mop : Mopt;
    begin
      GetSymbol;
      if Symbol= Letters
        then begin { Message prompt. }
          if Strings <> ''
            then begin
              Call('PRINT2');
              DefB(Length(Strings)-1);
              DefM(Strings);
            end;
          GetSymbol;
          if Symbol<> Semicolon
            then begin
              Error(erSN_ERR);
              Skip(fsys);
              Goto 1
           end;
          GetSymbol;
        end;    { Prompt. }
      { Store Variabre. }
      Ntemp := 0;
      Expression(s,fsys);
      if s.atk <> Vari
        then begin
          Error(erSN_ERR);
          Skip(fsys);
          Goto 1;
        end;
      if s.atbase
        then begin
          Scas1('LDP');
          ScAs1('PUSH')
        end;
      if s.AtStr
        then Call('INPUT1')
        else Call('INPUT2');
      AtToMop(s,Mop);
      if s.atbase
        then begin
          Scas1('POP');
          Scas1('STP')
        end
        else Lea(Mop);
      Exam;
 1:
    end; { Input statement. }

  procedure NextStatement;
    var x    : Attribute;
        Mop1 : Mopt;
        i    : 0..tmax;
    label    1;
    begin
      GetSymbol;
      if Symbol<> Identifier
        then begin
          Error(erSN_ERR);
          Skip(fsys);
          Goto 1
        end;
      Expression(x,fsys);
      AtToMop(x,Mop1);
      { Check <Variable> }
      if Fnum = 0
        then begin
          Error(erSN_ERR);    { 'Next without For' }
          Skip(fsys);
          Goto 1
        end;
      Fnum := Fnum -1;
      with ForTable[fnum] do
        if (Initvalue.Mopk  <> Mop1.Mopk)  or
           (Initvalue.xbase <> Mop1.xbase) or
           (Initvalue.xind  <> Mop1.xind )
          then begin
            Error(erSN_ERR);   { Next without For. }
            Skip(fsys);
            Goto 1
          end
        else begin
          case stepvalue.Mopk of
            Immed: begin
                     Lea(Mop1);
                     ScASM('ADIM  ',stepvalue.nimm)
                   end;
            Index: begin
                     Lda(stepvalue);
                     Lea(Mop1);
                     adm;
                   end;
            else   begin
                     Lea(Mop1);
                     adm
                   end
          end;
          ScASM('JP    N',Loopline);
          PutLabel(True,'X',LoopLine)
        end;
  1:
    end;


  procedure PrintStatement;
    var x    : Attribute;
        Mop1 : Mopt;
    begin
      GetSymbol;
      if Symbol= Letters
        then begin
          GetSymbol;
          if Strings =''
            then Call('PRINT7')
          else begin
            if Symbol<> Semicolon
              then Call('PRINT1')
              else begin
                Call('PRINT2');
                GetSymbol
              end;
            DefB(Length(Strings)-1);
            DefM(Strings)
          end
        end
      else { Expression. }
        begin
          if Not(Symbol in FactorHeader)
            then Call('PRINT7')
            else begin
              Ntemp := 0;
              Expression(x,fsys);
              AtToMop(x,Mop1);
              case x.atk of
                Cons: ScASM('LIB   ',x.atvalue);
                Vari: begin
                        Lda(Mop1);
                        Exab
                      end;
                Expr: Exab
              end;
              if Symbol= Semicolon
                then begin
                  if x.atstr
                    then Call('PRINT6')    { Bug fix 93.04.12 }
                    else Call('PRINT4');
                  GetSymbol
                end
              else
                if x.atstr
                  then Call('PRINT5')
                  else Call('PRINT3');
            end { Print Expression }
        end
    end; { Print statement }

  procedure PsetStatement;
    var   x,y       : Attribute;
          Mop1,Mop2 : Mopt;
    label 1;
    begin
      GetSymbol;
      Ntemp := 0;
      Expression(x,fsys);
      if x.atk = Expr
        then ScAs1('PUSH');
      if Symbol<> Comma
        then begin
          Error(erSN_ERR);
          Goto 1
        end;
      GetSymbol;
      Expression(y,fsys);
      AtToMop(x,Mop1);
      AtToMop(y,Mop2);
      case x.atk of
        Cons: case y.atk of
                Cons,
                Vari: begin
                        Lda(Mop1);
                        Ldb(Mop2)
                      end;
                Expr: begin
                        Ldb(Mop1);
                        Exab
                      end
              end;
        Vari: case y.atk of
                Cons: begin
                        Lda(Mop1);
                        Ldb(Mop2)
                      end;
                Vari: begin
                        Lda(Mop2);
                        Exab;
                        Lda(Mop1)
                      end;
                Expr: Ldb(Mop1)
              end;
        Expr: case y.atk of
                Cons,
                Vari: Ldb(Mop2);
                Expr: begin
                        Exab;
                        Scas1('POP');
                        Exab
                      end
              end;
      end;
      if Symbol<> RightParen
        then begin
          Error(erSN_ERR);
          Goto 1
        end;
      GetSymbol;
      if Symbol<> Comma
        then Call('PSET')
        else begin
          GetSymbol;
          if (Symbol<> Identifier) and (id<>'X       ')
            then begin
              Error(erSN_ERR);
              Goto 1
            end;
          Call('PSETX');
          GetSymbol
        end;
1:
    end;


  procedure ReadStatement;
    label 1;
    var x    : Attribute;
        Mop1 : Mopt;
    begin
      repeat
        GetSymbol;
        Call('READ');
        Ntemp := 0;
        Expression(x,fsys);
        AtToMop(x,Mop1);
        if x.atk <> Vari
          then begin
            Error(erSN_ERR);
            Skip(fsys);
            Goto 1
          end
          else begin
            Lea(Mop1);
            Exam
          end
      until Symbol<> Comma;
   1:
    end; { Read statement }


  procedure RemStatement;
    begin
      GetSymbol
    end;


  procedure RestoreStatement;
    begin
      GetSymbol;
      if Symbol<> Literal
        then Error(erSN_ERR);
      if Loclineno(IdValue) = 0
        then Reservation(IdValue);
      Call('RESTORE');
      WriteLn(ObjectTextFile,'         DW    L',IdValue);
      GetSymbol
    end;

  procedure ReturnStatement;
    begin
      Scas1('RTN');
      GetSymbol;
    end;


  procedure UsingStatement;
    begin
      GetSymbol;
      if Symbol <> Literal
        then begin
          Lp($1D);
          ScAs1('ANIM  0')
        end
        else begin
          if Not(IdValue in [2,3])
            then Error(erSN_ERR);
          Lp($1D);
          Lia(IdValue);
          Exam;
          GetSymbol
        end
    end;


  procedure WaitStatement;
    var x    : Attribute;
        Mop1 : Mopt;
    begin
      GetSymbol;
      if Symbol in FactorHeader
        then begin
          Expression(x,fsys);
          AtToMop(x,Mop1);
          case x.atk of
            Cons,
            Vari: Lda(Mop1);
            Expr:
          end;
          lp($21);
          Exam
        end
        else begin
          lp($21);
          Scas1('ORIM  0FFH')
        end
    end;

  procedure InlineStatement;
    var i:Byte;
    begin
      if Length(Strings) mod 2 <> 0
        then Error(erSN_ERR);
      DefH(Strings);
      GetSymbol
    end;

  procedure ExecuteStatement;
    begin
      case Symbol of
        SyBEEP   : BeepStatement;
        SyCLEAR  : ClearStatement;
        SyCLS    : ClsStatement;
        SyCURSOR : CursorStatement;
        SyDATA   : DataStatement;
        SyDIM    : DimStatement;
        SyEND    : EndStatement;
        SyFOR    : ForStatement;
        SyGCURSOR: GcursorStatement;
        SyGOSUB  : GosubStatement;
        SyGOTO   : GotoStatement;
        SyGPRINT : GprintStatement;
        SyIF     : ifStatement;
        SyINPUT  : InputStatement;
        SyNEXT   : NextStatement;
        SyPRESET : PresetStatement;
        SyPRINT  : PrintStatement;
        SyPSET   : PsetStatement;
        SyREAD   : ReadStatement;
        SyREM    : RemStatement;
        SyRESTORE: RestoreStatement;
        SyRETURN : ReturnStatement;
        SyUSING  : UsingStatement;
        SyWAIT   : WaitStatement;
        SyINLINE : InlineStatement;
        else Error(erSN_ERR)
      end
    end; { Execute statement }

  begin  { Statement }
    GetSymbol;
    if Symbol in StatementHeader
      then Executestatement
      else begin
        if Symbol= Identifier
          then Assignstatement
          else begin
            Error(erSN_ERR);
            Skip(fsys)
          end
      end
  end; { Statement }


{     1 line compiling       }

procedure OneLine;

  procedure EnterLabel;
    var i : Byte;
    begin
      TnkLabel := 'L'+IdStr+':';
      For i := 0 to 8-Length(TnkLabel)
        do TnkLabel := TnkLabel + ' '
    end;

  begin
    if Symbol= Literal
      then begin
        Enterlineno(IdValue);
        EnterLabel;
        repeat { Statement start }
          Statement;
          while Symbol= Colon
            do Statement;
        until Symbol= EndofLine;
        GetSymbol
      end
      else begin
        Error(erSN_ERR);
        Skip([EndofFile]);
        GetSymbol
      end
  end;


procedure ErrorCheck;
  begin

    { Check <Undefined lineno> }
    For k := 0 to rnum -1 do
      if loclineno(rtable[k]) = 0
        then begin
          WriteLn('** undefined line no.');
          ErrorDetect := True;
        end;

    { Check <Next without for> }
    if fnum < 0
      then begin
        WriteLn('** Next without For.');
        ErrorDetect := True;
      end;

    { Check <For without Next }
    if fnum > 0
      then begin
        WriteLn('** For without Next.');
        ErrorDetect := True;
      end;

  end;


procedure DispNendMsg;
  begin
    WriteLn;
    WriteLn('    No error.');
  end;


{ Display error message.   }

procedure DispErrorMsg;
  begin
    WriteLn;
    WriteLn('    Total errors. = ',enum);
    for i := 1 to enum do
      with Errtable[i] do
         WriteLn(SourceFileName,
                 ' Line   ',  cnt:3,
                 ' Column ',  pos:2,
                 ': Error ', Ord(erno):2,
                 ' ', ErrMsg[erno]   )
  end; { Display error message }


{ Opeaning message. }

procedure Opening;
  begin
    WriteLn('TNKB Copyright (c) 1993 K.Watanuki');
    WriteLn;
    WriteLn(ObjectTextFile,';');
    WriteLn(ObjectTextFile,';   ',SourceFileName );
    WriteLn(ObjectTextFile,';');
    WriteLn(ObjectTextFile,'     INCLUDE "RUNTIME.H"')
  end;

{ Ending message.  }

procedure Ending;
  begin
    WriteLn;
    WriteLn('Compile end.');
    WriteLn(ObjectTextFile,';              ');
    WriteLn(ObjectTextFile,'; End of text. ');
    WriteLn(ObjectTextFile,';              ');
  end; { Ending message }


procedure TableSetup;
  var i : Byte;

  procedure SetRw(Sy: SymbolKind; RwName: IdName);
    var j: Byte;
    begin
      Rw[I]   := RwName;
      For J := 1 to 8-Length(RwName) do
        Rw[I] := Rw[I] + ' ';
      SyRw[I] := Sy;
      Inc(I);
    end;
  begin
    I := 1;
    SetRw(SyAND,    'AND'    );  SetRw(SyBEEP,   'BEEP'    );
    SetRw(SyCLEAR,  'CLEAR'  );  SetRw(SyCLS,    'CLS'     );
    SetRw(SyCURSOR, 'CURSOR' );  SetRw(SyDATA,   'DATA'    );
    SetRw(SyDIM,    'DIM'    );  SetRw(SyEND,    'END'     );
    SetRw(SyFOR,    'FOR'    );  SetRw(SyGCURSOR,'GCURSOR(');
    SetRw(SyGOSUB,  'GOSUB'  );  SetRw(SyGOTO,   'GOTO'    );
    SetRw(SyGPRINT, 'GPRINT' );  SetRw(SyIF,     'IF'      );
    SetRw(SyINPUT,  'INPUT'  );  SetRw(SyLET,    'LET'     );
    SetRw(SyNEXT,   'NEXT'   );  SetRw(SyON,     'ON'      );
    SetRw(SyOr,     'OR'     );  SetRw(SyPRESET, 'PRESET(' );
    SetRw(SyPRINT,  'PRINT'  );  SetRw(SyPSET,   'PSET('   );
    SetRw(SyREAD,   'READ'   );  SetRw(SyREM,    'REM'     );
    SetRw(SyRESTORE,'RESTORE');  SetRw(SyRETURN, 'RETURN'  );
    SetRw(SySTEP,   'STEP'   );  SetRw(SyTHEN,   'THEN'    );
    SetRw(SyTO,     'TO'     );  SetRw(SyUSING,  'USING'   );
    SetRw(SyWAIT,   'WAIT'   );

    SySc[')'] := RightParen;   SySc['*'] := Asterisk;
    SySc['('] := LeftParen;    SySc['/'] := Slant;
    SySc['+'] := Plus;         SySc[','] := Comma;
    SySc['-'] := Minus;        SySc[';'] := Semicolon;
    SySc['='] := SyEQ;         SySc['#'] := Sharp;
    SySc[':'] := Colon;
  end; { Table Set up }


{     Initialize every work.     }

procedure Initialize;
  begin

    ErrorDetect := False;

    Hord['0'] :=  0; Hord['1'] :=  1; Hord['2'] :=  2; Hord['3'] :=  3;
    Hord['4'] :=  4; Hord['5'] :=  5; Hord['6'] :=  6; Hord['7'] :=  7;
    Hord['8'] :=  8; Hord['9'] :=  9; Hord['A'] := 10; Hord['B'] := 11;
    Hord['C'] := 12; Hord['D'] := 13; Hord['E'] := 14; Hord['F'] := 15;

    ll := 0;
    cc := 0;
    ch := ' ';

    TableSetup;
    t  := 0;
    EnterFunctionId;
    TopId     := 0;
    LastId    := t;
    braline   := 1;
    ifLine    := 1;
    lnum      := 0;
    Rnum      := 0;
    Fnum      := 0;
    ForLine   := 0; { For-Next relation register.        }
    NewAddr   := 0; { Variable address of <INTERNAL RAM> }
    ltable[0] := 0;
    StatementHeader :=
                   [ SyBEEP,   SyCLEAR,  SyCLS,    SyCURSOR, SyDATA,
                     SyDIM,    SyEND,    SyFOR,    SyGCURSOR,SyGOSUB,
                     SyGOTO,   SyGPRINT, SyIF,     SyINPUT,  SyLET,
                     SyNEXT,   SyPRESET, SyPRINT,  SyPSET,   SyREAD,
                     SyREM,    SyRESTORE,SyRETURN, SyUSING,  SyWAIT,
                     SyINLINE
                   ];
    FactorHeader := [Literal, Identifier, LeftParen, Letters];
    Isfin   := false;   { CLear Finish flag.       }
    InCount := 0;       { CLear Source line count. }
    Enum    := 0;       { CLear Total error count. }
  end;

{     Text file open.     }

procedure TextFileOpen;

  function Isfile(F : FileName) : Boolean;
    var  I,J    :  Word;

    procedure Emit; { Emit Filename. }
      begin
        SourceFileName := SourceFileName + Upcase(F[I]);
        I := I + 1;
      end;

    begin
      I := 1;
      SourceFileName := '';
      if Not (Upcase(F[1]) in ['A'..'Z'])
        then Isfile := False
        else begin
          Emit;
          while (Upcase(F[I]) in ['0'..'9','A'..'Z']) and
                (I<9) and ( I <= Length(F) ) do
            Emit;
          ObjectFileName := SourceFileName + '.ASC';
          if F[I] = '.'
            then begin
              Emit;
              J := 1;
              while ( Upcase(F[I]) in ['0'..'9','A'..'Z'] ) and
                    (J<4) and ( I <= Length(F) ) do
                begin
                  Emit;
                  J := J + 1
                end;
              Isfile := True
            end
            else begin
              if Length(F)+1 = I
                then begin
                  SourceFileName := SourceFileName + '.TNK';
                  Isfile := True
                end
                else begin
                  SourceFileName := SourceFileName + F[I];
                  Isfile := False
                end
            end
        end
    end;  { Is filename ? }

  begin
    FileFail := False;
    repeat
      G := '';
      if FileFail or
        (Isfile(ParamSTR(1)) = False)
      then
        repeat
          Write(' Source file : ');
          G := '';
          ReadLn(G);
          if Ord(G[0]) = 0
            then Halt;
        until Isfile(G);
      Assign(SourceTextFile, SourceFileName);
      {$I-}
      ReSet(SourceTextFile);
      {$I+}
      if IOResult = 0
        then FileFail := False
        else begin
          WriteLn('File Not found.');
          FileFail := True;
        end
    until Not(FileFail);
    Assign(ObjectTextFile, ObjectFileName);
    ReWrite(ObjectTextFile);
  end;

label 2;

procedure Test1;
var o: Integer;
  procedure GetToken;
  begin
    GetSymbol;
    o := Ord(Symbol);
    case Symbol of
    Identifier:
      WriteLn('Identifier =',Id);
    Literal:
      WriteLn('Literal =',IdStr);
    BadSymbol:
      WriteLn('Bad! order=', Ord(ch) );
    EndofLine:
      WriteLn('End of Line');
    EndofFile:
      WriteLn('End of File');
    else
      begin
        if Symbol in [
                   { Rerational operator }
                   SyLT,  SyLE, SyNE, SyEQ, SyGE, SyGT
                     ]
        then
          WriteLn('Operator(R)=',Ord(Symbol));
        if Symbol in [
                          { Logical operator }
                          SyAND, syOR, syEOR
                     ]
        then
          WriteLn('Operator(L)=',Ord(Symbol));
        if Symbol in [
                   { Alithmetic operator }
                   LeftParen, RightParen,  Asterisk,
                   Plus,      Minus,       Slant
                     ]
        then
          WriteLn('Operator(A)=',Ord(Symbol));
        if Symbol in [
                   SyBEEP,   SyCLEAR,  SyCLS,    SyCURSOR, SyDATA,
                   SyDIM,    SyEND,    SyFOR,    SyGCURSOR,SyGOSUB,
                   SyGOTO,   SyGPRINT, SyIF,     SyINPUT,  SyLET,
                   SyNEXT,   SyPRESET, SyPRINT,  SyPSET,   SyREAD,
                   SyREM,    SyRESTORE,SyRETURN, SySTEP,   SyTO,
                   SyTHEN,   SyUSING,  SyWAIT,   SyINLINE, SyON
                   ]
        then
          WriteLn('Reserved=',Id);

      end;
    end;
  end;
begin
  GetToken;
  while Not (Symbol = EndofFile) do
  begin
    repeat
      GetToken;
    until Symbol = EndofLine;
    GetToken;
  end;
end;

procedure Test0;
  procedure TestLine;
  begin
    Read(SourceTextFile,SourceTextLine);
    for cc:=1 to Length(SourceTextLine) do
      Write('+',SourceTextLine[cc]);
    if EoLn(SourceTextFile) then
      WriteLn('+EOL');
    ReadLn(SourceTextFile);
    WriteLn;
  end;
begin
  TestLine;
  TestLine;
end;

procedure Processing;
begin
  GetSymbol;
  while Symbol <> EndofFile do
    Oneline;
  if Not(Isfin)
    then Call('BYE');
  ErrorCheck;
  if ErrorDetect
    then DispErrorMsg
    else DispNendMsg
end;

procedure Done;
begin
  Close(SourceTextFile);
  Close(ObjectTextFile);
end;

begin
  Initialize;
  TextFileOpen;
  Opening;
  Processing;
  Ending;
  Done;
end.
