import sys
from collections import namedtuple
import ply.lex as lex
import ply.yacc as yacc

Statement=namedtuple("Statement","cmd val1 val2 lineno")
DeviceStatement=namedtuple("DeviceStatement","devid val1 val2 lineno")
CodeLabel=namedtuple("CodeLabel","id lineno")
Alias=namedtuple("Alias","dict statement lineno")
IfWhile=namedtuple("IfWhile","type pred statement lineno")
IfElse=namedtuple("IfElse","type pred statementif statementelse lineno")
Define=namedtuple("Define","id val lineno")
Data=namedtuple("Data","id val lineno")
Var=namedtuple("Var","decl lineno")
Declaration=namedtuple("Declaration","id val lineno")
RegStore=namedtuple("Store","storeset statement lineno")
ArrayAccess=namedtuple("ArrayAccess","id index")
Register=namedtuple("Register","val")
MemoryRegister=namedtuple("MemoryRegister","val")
MemRegPair=namedtuple("MemRegPair","mem reg")
OpExpression=namedtuple("OpExpression","op op1 op2 lineno")
StatementList=namedtuple("StatementList","astid isloop statements lineno")
RegAssign=namedtuple("RegAssign","numuse assigns")
TempVar=namedtuple("TempVar","id")
BreakCont=namedtuple("BreakCont","type val lineno")
Return=namedtuple("Return","expr lineno")
Function=namedtuple("Function","name args statement lineno")
FunctionCall=namedtuple("FunctionCall","name args lineno")

INTEGER_MASK=0x20000000
DATA_MASK=0x1FFFFFFF
REGISTER_MASK=0x200
NUMBER_MASK=0x1FF
ops=["SHUTDOWN","MOV","LOAD","STORE","AND","OR","XOR","NOTAND","SHL","SHR","INC","DEC","ADD","SUB","GNZ","GN"]
opcodes={"SHUTDOWN":0,"MOV":1,"LOAD":2,"STORE":3,"AND":4,"OR":5,"XOR":6,"NOTAND":7,"SHL":8,"SHR":9,"INC":10,"DEC":11,"ADD":12,"SUB":13,"GNZ":14,"GN":15}
DEVICE_CMD_CODE=16
CMD_OFFSET=20
ARG1_OFFSET=10
NUM_REGISTERS=15
NUM_USABLE_REGISTERS=12
VAL1_REGISTER=Register(13)
VAL2_REGISTER=Register(12)
LOOP_MULTIPLIER=100
ARG_LIMIT=0x100

numerrors=0

def translate_line(line):
	if line==-1:
		return "unknown"
	else:
		return str(line)

def print_error(message,line):
	global numerrors
	numerrors+=1
	print("Error (line %s): %s" % (translate_line(line),message))

def print_critical_error(message,line):
	global numerrors
	numerrors+=1
	print("Critical error (line %s): %s" % (translate_line(line),message))
	print("Critical errors indicate that there may be a bug with assembler.py. Please report such bugs to mark2222.")
	
def print_warning(message,line):
	print("Warning (line %s): %s" % (translate_line(line),message))

tokens = (
	"TRIOP","CMD","BINOP","UNOP",
	"NUMBER","REGISTER","CODELABEL","ID",
	"VAR","DATA","ALIAS","IF","ELSE","WHILE","DEFINE","DO","REGSTORE",
	"OPENBRACKET","CLOSEBRACKET","OPENBRACE","CLOSEBRACE","OPENSQUARE","CLOSESQUARE",
	"EQUALS","COMMA","PLUSMINUS","INCDEC","BITWISEOP","NOT","MUTABLEBINOP","COMPARE",
	"BOOLAND","BOOLOR","BOOLNOT",
	"FUNC","RETURN","FUNCID","BREAKCONT"
    )

unops={"INC","DEC","GOTO"}
triops={"DEV"}
binops={"MOV","LOAD","STORE","AND","OR","XOR","NOTAND","SHL","SHR","ADD","SUB","GNZ","GN"}
cmds={"SHUTDOWN"}
binopswithregstore={"MOV","LOAD","AND","OR","XOR","NOTAND","SHL","SHR","ADD","SUB"}
unopswithregstore={"INC","DEC"}
gotobinops={"GNZ","GN"}
modifyexpops={"=","+=","-=","&=","|=","~&=","^=","<<=",">>=","++","--"}
unexpops={"!","~","neg","++","--"}
expoptoop={"++":"INC","--":"DEC",
		"=":"MOV","+=":"ADD","-=":"SUB","&=":"AND","|=":"OR","~&=":"NOTAND","^=":"XOR","<<=":"SHL",">>=":"SHR",
		"+":"ADD","-":"SUB","&":"AND","|":"OR","~&":"NOTAND","^":"XOR","<<":"SHL",">>":"SHR",
		"~=":"XOR"}
compexpops={"<",">","<=",">=","==","~="}
boolops={"!","&&","||"}
commutativeops={"+","&","|","^","~="}

assigned={}
codelabels={}
codelabelset=set()
defines={}
datainit=[]
reldatapointers={}
unravelledstatements=[]
numsyscodelabels=0
numsysdata=0
numsysvar=0
varassigns={}
numastnodes=0
variables=set()
varnames={}
usagecnt={}
continues=[]
breaks=[]
funcs={}
cfunc="$"
retcodelabel=None

t_OPENBRACKET=r"\("
t_CLOSEBRACKET=r"\)"
t_OPENBRACE=r"{"
t_CLOSEBRACE=r"}"
t_OPENSQUARE=r"\["
t_CLOSESQUARE=r"\]"
t_COMMA=r","
t_EQUALS=r"="
t_INCDEC=r"(\+\+)|(\-\-)"
t_BOOLAND="\&\&"
t_BOOLOR="\|\|"
t_MUTABLEBINOP=r"(\&|\||(\<\<)|(\>\>)|\^|(\~\&)|\+|\-)\="
t_COMPARE=r"(\<|\>\=?)|(\=\=)|(\~\=)"
t_PLUSMINUS=r"\+|\-"
t_BITWISEOP=r"\&|\||(\<\<)|(\>\>)|\^|(\~\&)"
t_NOT=r"\~"
t_BOOLNOT="\!"

def t_hexnumber(t):
	r"0x(\d|[a-fA-F])+"
	try:
		t.value=int(t.value[2:],16)
	except ValueError:
		print_error("Integer value too large: %s"%t.value,t.lineno)
		t.value=0
	t.type="NUMBER"
	return t

def t_binnumber(t):
	r"\d+b"
	try:
		t.value=int(t.value[:-1],2)
	except ValueError:
		print_error("Integer value too large: %s"%t.value,t.lineno)
		t.value=0
	t.type="NUMBER"
	return t

def t_NUMBER(t):
	r"\d+"
	try:
		t.value=int(t.value)
	except ValueError:
		print_error("Integer value too large: %s"%t.value,t.lineno)
		t.value=0
	return t

def t_CODELABEL(t):
	r":[a-zA-Z][a-zA-Z0-9]*"
	t.value=t.value[1:]
	return t

def t_FUNCID(t):
	r"\@[a-zA-Z][a-zA-Z0-9]*"
	t.value=t.value[1:]
	return t
	
def t_ID(t):
	r"[a-zA-Z0-9_]+"
	if t.value in unops:
		t.type="UNOP"
	elif t.value in binops:
		t.type="BINOP"
	elif t.value in triops:
		t.type="TRIOP"
	elif t.value in cmds:
		t.type="CMD"
	elif t.value=="data":
		t.type="DATA"
	elif t.value=="var":
		t.type="VAR"
	elif t.value=="alias":
		t.type="ALIAS"
	elif t.value=="define":
		t.type="DEFINE"
	elif t.value=="ifnn" or t.value=="ifz" or t.value=="if":
		t.type="IF"
	elif t.value=="else":
		t.type="ELSE"
	elif t.value=="while" or t.value=="whilen":
		t.type="WHILE"
	elif t.value=="do":
		t.type="DO"
	elif t.value=="regstore":
		t.type="REGSTORE"
	elif t.value=="func":
		t.type="FUNC"
	elif t.value=="return":
		t.type="RETURN"
	elif t.value=="break" or t.value=="continue":
		t.type="BREAKCONT"
	elif t.value[0]=="r" and t.value[1:].isdigit():
		t.type="REGISTER"
		try:
			t.value=int(t.value[1:])
		except ValueError:
			print_error("Integer value too large: %s"%t.value,t.lineno)
			t.value=0
		if t.value<0 or t.value>=NUM_REGISTERS:
			print_error("Register does not exist (only %d registers allowed): r%d"%(NUM_REGISTERS,t.value),t.lineno)
			t.value=0
		t.value=Register(t.value)
	return t

# Ignored characters
t_ignore = " \t"

def t_comment(t):
	r"(//.*)|(/\*(.|\n)*?\*/)"

def t_newline(t):
	r"\n+"
	numlines=t.value.count("\n")
	t.lexer.lineno+=numlines

def t_error_danglingcomment(t):
	r"/\*(.|\n)*?"
	print_error("Dangling multiline comment",t.lineno)
    
def t_error(t):
    print_error("Illegal character '%s'" % t.value[0],t.lineno)
    t.lexer.skip(1)

precedence = (
	("left","EXPR","RET"),
	("right","THEN","ELSE"),
	("right","NEGATE"),
	("left","BOOLOR"),
	("left","BOOLAND"),
	("right","BOOLNOT"),
	("nonassoc","COMPARE"),
	("left","INCDEC"),
	("left","MUTABLEBINOP","EQUALS"),
	("left","PLUSMINUS"),
	("left","BITWISEOP"),
	("right","NOT")
)

def p_statementlist_statementlist(p):
	"statementlist : statementlist statement"
	p[0]=p[1]+[p[2]]

def p_statementlist_statement(p):
	"statementlist : statement"
	p[0]=[p[1]]

def p_statement_statementlist(p):
	"statement : OPENBRACE statementlist CLOSEBRACE"
	p[0]=p[2]

def p_statement_nothing(p):
	"statement : OPENBRACE CLOSEBRACE"
	p[0]=[]

def p_statement_cmd(p):
	"statement : CMD"
	p[0]=Statement(p[1],0,0,p.lineno(1))
	
def p_statement_unop(p):
	"statement : UNOP argument"
	if p[1]=="GOTO":
		p[0]=Statement("GNZ",1,p[2],p.lineno(1))
	else:
		p[0]=Statement(p[1],p[2],0,p.lineno(1))

def p_statement_binop(p):
	"statement : BINOP argument argument"
	p[0]=Statement(p[1],p[2],p[3],p.lineno(1))

def p_statement_binop_codelabel(p):
	"statement : BINOP argument CODELABEL"
	print_warning("Code label :%s used as argument - colon can be omitted"%p[3],p.lineno(1))
	p[0]=Statement(p[1],p[2],p[3],p.lineno(1))
	
def p_statement_triop(p):
	"statement : TRIOP argument argument argument"
	if p[1]=="DEV":
		if isinstance(p[1],Register):
			print_error("Device identifier cannot be a register",p.lineno(1))
		elif isinstance(p[1],ArrayAccess):
			print_error("Device identifier cannot be an array access",p.lineno(1))
		else:
			p[0]=DeviceStatement(p[2],p[3],p[4],p.lineno(1))
	else:
		print_critical_error("Unimplemented ternary operation %s"%p[1],p.lineno(1))

def p_statement_codelabel(p):
	"statement : CODELABEL"
	p[0]=CodeLabel(p[1],p.lineno(1))

def p_statement_define(p):
	"statement : DEFINE ID argument"
	p[0]=Define(p[2],p[3],p.lineno(1))

def p_statement_alias(p):
	"statement : ALIAS OPENBRACKET aliaslist CLOSEBRACKET statement"
	p[0]=Alias(p[3],p[5],p.lineno(1))

def p_statement_data(p):
	"""statement    : DATA ID EQUALS NUMBER
					| DATA ID EQUALS array"""
	p[0]=Data(p[2],p[4],p.lineno(1))

def p_statement_var(p):
	"statement : VAR declarationlist"
	p[0]=Var(p[2],p.lineno(1))

def p_statement_ifwhile(p):
	"statement : IF OPENBRACKET expression CLOSEBRACKET statement %prec THEN"
	p[0]=IfWhile(p[1],p[3],p[5],p.lineno(1))

def p_statement_do(p):
	"statement : DO statement WHILE OPENBRACKET expression CLOSEBRACKET"
	p[0]=IfWhile(p[1]+p[3],p[5],p[2],p.lineno(1))

def p_statement_ifelse(p):
	"statement : IF OPENBRACKET expression CLOSEBRACKET statement ELSE statement"
	p[0]=IfElse(p[1],p[3],p[5],p[7],p.lineno(1))

def p_statement_regstore(p):
	"statement : REGSTORE OPENBRACKET argumentlist CLOSEBRACKET statement"
	p[0]=RegStore(p[3],p[5],p.lineno(1))

def p_statement_expression(p):
	"statement : expression %prec EXPR"
	p[0]=p[1]

def p_statement_breakcont(p):
	"statement : BREAKCONT NUMBER"
	p[0]=BreakCont(p[1],p[2],p.lineno(1))

def p_statement_return(p):
	"statement : RETURN expression %prec RET"
	p[0]=Return(p[2],p.lineno(1))

def p_statement_func(p):
	"statement : FUNC ID OPENBRACKET idlist CLOSEBRACKET statement"
	p[0]=Function(p[2],p[4],p[6],p.lineno(1))

def p_idlist_idlist(p):
	"idlist : idlist COMMA ID"
	p[0]=p[1]+[p[3]]

def p_idlist_id(p):
	"idlist : ID"
	p[0]=[p[1]]

def p_expression_bracket(p):
	"expression : OPENBRACKET expression CLOSEBRACKET"
	p[0]=p[2]

def p_expression_binop(p):
	"""expression : expression MUTABLEBINOP expression
				  | expression COMPARE expression
				  | expression PLUSMINUS expression
				  | expression BITWISEOP expression
				  | expression BOOLAND expression
				  | expression BOOLOR expression
				  | expression EQUALS expression"""
	p[0]=OpExpression(p[2],p[1],p[3],p.lineno(2))

def p_expression_unop(p):
	"""expression : NOT expression
				  | BOOLNOT expression"""
	p[0]=OpExpression(p[1],p[2],None,p.lineno(1))

def p_expression_incdec(p):
	"expression : expression INCDEC"
	p[0]=OpExpression(p[2],p[1],None,p.lineno(2))

def p_expression_argument(p):
	"expression : argument"
	p[0]=p[1]

def p_expression_funcid(p):
	"expression : FUNCID OPENBRACKET expressionlist CLOSEBRACKET"
	p[0]=FunctionCall(p[1],p[3],p.lineno(1))

def p_expressionlist_expressionlist(p):
	"expressionlist : expressionlist COMMA expression"
	p[0]=p[1]+[p[3]]

def p_expressionlist_expression(p):
	"expressionlist : expression"
	p[0]=[p[1]]

def p_declarationlist_declarationlist(p):
	"declarationlist : declarationlist COMMA declaration"
	p[0]=p[1]+[p[3]]

def p_declarationlist_declaration(p):
	"declarationlist : declaration"
	p[0]=[p[1]]

def p_declaration_id(p):
	"declaration : ID"
	p[0]=Declaration(p[1],None,p.lineno(1))

def p_declaration_expression(p):
	"declaration : ID EQUALS expression"
	p[0]=Declaration(p[1],p[3],p.lineno(1))

def p_array(p):
	"array : OPENBRACE numberlist CLOSEBRACE"
	p[0]=p[2]

def p_numberlist_numberlist(p):
	"numberlist : numberlist COMMA NUMBER"
	p[0]=p[1]+[p[3]]

def p_numberlist_number(p):
	"numberlist : NUMBER"
	p[0]=[p[1]]

def p_aliaslist_aliasstatement(p):
	"aliaslist : aliasstatement"
	p[0]=p[1]

def p_aliaslist_aliaslist(p):
	"aliaslist : aliaslist COMMA aliasstatement"
	p[0]=p[1]
	p[0].update(p[3])
	
def p_aliasstatement(p):
	"aliasstatement : ID EQUALS REGISTER"
	p[0]={p[1]:p[3]}

def p_argumentlist_argumentlist(p):
	"argumentlist : argumentlist COMMA argument"
	p[0]=p[1]+[p[3]]

def p_argumentlist_argument(p):
	"argumentlist : argument"
	p[0]=[p[1]]

def p_argument(p):
	"""argument : NUMBER
				| REGISTER"""
	p[0]=p[1]

def p_argument_negnumber(p):
	"argument : PLUSMINUS NUMBER %prec NEGATE"
	if p[1]=="-":
		p[0]=-p[2]
	else:
		p[0]=p[2]

def p_argument_arrayaccess(p):
	"argument : ID OPENSQUARE NUMBER CLOSESQUARE"
	p[0]=ArrayAccess(p[1],p[3])

def p_argument_id(p):
	"argument : ID"
	p[0]=p[1]

def p_error(t):
	if t is None:
		print("Syntax error at unknown token")
	else:
		print_error("Syntax error at token %s"%t.type,t.lineno)
		yacc.errok()

def checkval(x,lineno):
	if isinstance(x,str):
		if x in codelabels:
			return True,codelabels[x]
		elif x in reldatapointers:
			return True,len(unravelledstatements)+reldatapointers[x]
		else:
			print_critical_error("Unknown identifier %s"%x,lineno)
			return False,None
	elif isinstance(x,int):
		if x<-ARG_LIMIT or x>=ARG_LIMIT:
			print_error("Integer literal %d out of range [-256,256)"%x,lineno)
			return False,None
		else:
			return True,x&NUMBER_MASK
	elif isinstance(x,Register):
		return True,x.val|REGISTER_MASK
	elif isinstance(x,ArrayAccess):
		if x.id in reldatapointers:
			return True,len(unravelledstatements)+reldatapointers[x.id]+x.index
		elif x.id in assigned:
			print_error("Array access on non-data pointer %s"%x.id,lineno)
		else:
			print_error("Unknown identifier %s"%x.id,lineno)
			return False,None
	else:
		print_critical_error("Unknown AST type %s"%x.__class__.__name__,lineno)
		return False,None

def decodeval(x):
	if x>=512:
		return "r"+str(x-512)
	else:
		return str(x)

def emitstatement(s):
	isvalid=True
	cvalid,checkret=checkval(s.val1,s.lineno)
	if cvalid:
		s=s._replace(val1=checkret)
	else:
		isvalid=False
	cvalid,checkret=checkval(s.val2,s.lineno)
	if cvalid:
		s=s._replace(val2=checkret)
	else:
		isvalid=False
	if isvalid:
		if s.cmd[0:3]=="DEV":
			s=s._replace(cmd=DEVICE_CMD_CODE|int(s.cmd[3:]))
		else:
			s=s._replace(cmd=opcodes[s.cmd])
		outputfile.write("%08x\n"%(INTEGER_MASK|
								(s.cmd<<CMD_OFFSET)|
								(s.val1<<ARG1_OFFSET)|
								s.val2))
		if (s.cmd&DEVICE_CMD_CODE)!=0:
			intfile.write("DEV %d %s %s\n"%(s.cmd-DEVICE_CMD_CODE,decodeval(s.val1),decodeval(s.val2)));
		else:
			intfile.write("%s %s %s\n"%(ops[s.cmd],decodeval(s.val1),decodeval(s.val2)));

def getsyscodelabel(lineno):
	global numsyscodelabels
	global codelabelset
	nextcodelabel="$scl"+str(numsyscodelabels)
	numsyscodelabels+=1
	codelabelset|={nextcodelabel}
	assigned[nextcodelabel]=lineno
	return CodeLabel(nextcodelabel,lineno)

def getsysdata(lineno,init=0):
	global numsysdata
	global datainit
	nextsysdata="$sd"+str(numsysdata)
	numsysdata+=1
	reldatapointers[nextsysdata]=len(datainit)
	datainit+=[init]
	assigned[nextsysdata]=lineno
	return nextsysdata

def getsysvar():
	global numsysvar
	nextsysvar="$sv"+str(numsysvar)
	numsysvar+=1
	return nextsysvar

def unravelstructure(s):
	global numastnodes
	global unravelledstatements
	if isinstance(s,StatementList):
		for cstatement in s.statements:
			unravelstructure(cstatement)
	elif isinstance(s,Statement):
		memoryloads=[]
		memorystores=[]
		if isinstance(s.val1,str) and s.val1 in varassigns:
			if isinstance(varassigns[s.val1],MemoryRegister):
				if s.cmd!="MOV" and s.cmd!="LOAD":
					memoryloads+=[MemRegPair(varassigns[s.val1].val,VAL1_REGISTER)]
				memorystores+=[MemRegPair(varassigns[s.val1].val,VAL1_REGISTER)]
				s=s._replace(val1=VAL1_REGISTER)
			else:
				s=s._replace(val1=varassigns[s.val1])
		if isinstance(s.val2,str) and s.val2 in varassigns:
			if isinstance(varassigns[s.val2],MemoryRegister):
				memoryloads+=[MemRegPair(varassigns[s.val2].val,VAL2_REGISTER)]
				s=s._replace(val2=VAL2_REGISTER)
			else:
				s=s._replace(val2=varassigns[s.val2])
		if len(memoryloads)==0 and len(memorystores)==0:
			unravelledstatements+=[s]
		else:
			newstatementlist=[]
			for cload in memoryloads:
				newstatementlist+=[Statement("LOAD",cload.reg,cload.mem,s.lineno)]
			newstatementlist+=[s]
			for cstore in memorystores:
				newstatementlist+=[Statement("STORE",cstore.mem,cstore.reg,s.lineno)]
			clistid=numastnodes
			numastnodes+=1
			unravelstructure(StatementList(clistid,False,newstatementlist,s.lineno))
	elif isinstance(s,CodeLabel):
		codelabels[s.id]=len(unravelledstatements)
		assigned[s.id]=s.lineno
	elif isinstance(s,Var):
		pass
	elif s is not None:
		print_critical_error("Unknown AST type (%s)"%s.__class__.__name__,s.lineno)

def assignreg(reg,vars):
	if isinstance(vars,str):
		varassigns[vars]=reg
	else:
		for cvar in vars:
			assignreg(reg,cvar)

def allocateregisters(s):
	newvars=[]
	regassigns=[]
	for i in range(NUM_USABLE_REGISTERS):
		regassigns+=[RegAssign(0,[])]
	for cstatement in s.statements:
		if isinstance(cstatement,Var):
			newvars+=[cstatement.decl]
		elif isinstance(cstatement,StatementList):
			nassign=allocateregisters(cstatement)
			for i in range(NUM_USABLE_REGISTERS):
				newnumuse=regassigns[i].numuse+nassign[i].numuse
				if newnumuse>1000000000:
					newnumuse=1000000000
				regassigns[i]=RegAssign(newnumuse,[regassigns[i].assigns,nassign[i].assigns])
	newvars.sort(key=lambda x:usagecnt[x],reverse=True)
	newvarptr=0
	regassignptr=0
	fassigns=[]
	while newvarptr<len(newvars) or regassignptr<len(regassigns):
		if regassignptr<len(regassigns) and (newvarptr>=len(newvars) or usagecnt[newvars[newvarptr]]<regassigns[regassignptr].numuse):
			nregassign=regassigns[regassignptr]
			regassignptr+=1
		else:
			nregassign=RegAssign(usagecnt[newvars[newvarptr]],newvars[newvarptr])
			newvarptr+=1
		if nregassign.numuse>0:
			if len(fassigns)>=NUM_USABLE_REGISTERS:
				assignreg(MemoryRegister(getsysdata(s.lineno)),nregassign.assigns)
			else:
				fassigns+=[nregassign]
	while len(fassigns)<NUM_USABLE_REGISTERS:
		fassigns+=[RegAssign(0,[])]
	if s.isloop:
		for i in range(len(fassigns)):
			if fassigns[i].numuse<=10000000:
				fassigns[i]._replace(numuse=fassigns[i].numuse*LOOP_MULTIPLIER)
			else:
				fassigns[i].numuse=1000000000
	return fassigns

def touniquevarname(origname):
	appendix=0
	if origname in varnames:
		appendix=varnames[origname]
	return origname+"_"+str(appendix)

def incrementvarnamecnt(origname):
	if origname in varnames:
		varnames[origname]+=1
	else:
		varnames[origname]=1

def translateval(x,lineno):
	if isinstance(x,str):
		if x in codelabelset or x in reldatapointers or x in variables:
			return True,x
		elif x in defines:
			return True,defines[x]
		else:
			print_error("Undefined identifier %s"%x,lineno)
			return False,None
	elif isinstance(x,int) or isinstance(x,Register) or isinstance(x,ArrayAccess):
		return True,x
	else:
		print_critical_error("Unknown AST type (%s)"%x.__class__.__name__,lineno)
		return False,None

def simplifyexpression(exp):
	if isinstance(exp,OpExpression):
		if exp.op in unexpops:
			if exp.op=="~":
				return simplifyexpression(OpExpression("~&",exp.op1,-1,exp.lineno))
			elif exp.op=="neg":
				return simplifyexpression(OpExpression("-",0,exp.op1,exp.lineno))
			else:
				return exp
		elif exp.op in compexpops:
			if exp.op=="==":
				return simplifyexpression(OpExpression("!",OpExpression("^",exp.op1,exp.op2,exp.lineno),None,exp.lineno))
			elif exp.op=="~=":
				return simplifyexpression(OpExpression("^",exp.op1,exp.op2,exp.lineno))
			elif exp.op==">":
				return simplifyexpression(OpExpression("<",exp.op2,exp.op1,exp.lineno))
			elif exp.op=="<=":
				return simplifyexpression(OpExpression("!",OpExpression("<",exp.op2,exp.op1,exp.lineno),None,exp.lineno))
			elif exp.op==">=":
				return simplifyexpression(OpExpression("!",OpExpression("<",exp.op1,exp.op2,exp.lineno),None,exp.lineno))
			else:
				return exp
		else:
			return exp
	else:
		return exp

def replacearguments(s,argdict):
	if isinstance(s,OpExpression):
		return OpExpression(s.op,replacearguments(s.op1,argdict),replacearguments(s.op2,argdict),s.lineno)
	elif isinstance(s,FunctionCall):
		return FunctionCall(s.name,[replacearguments(x,argdict) for x in s.args],s.lineno)
	elif isinstance(s,int) or isinstance(s,Register) or isinstance(s,CodeLabel) or isinstance(s,Define) or isinstance(s,Data) or isinstance(s,BreakCont):
		return s
	elif isinstance(s,str):
		if s in argdict:
			return argdict[s]
		else:
			return s
	elif isinstance(s,list):
		return [replacearguments(x,argdict) for x in s]
	elif isinstance(s,Function):
		return None
	elif isinstance(s,Statement):
		return Statement(s.cmd,replacearguments(s.val1,argdict),replacearguments(s.val2,argdict),s.lineno)
	elif isinstance(s,DeviceStatement):
		return DeviceStatement(replacearguments(s.devid,argdict),replacearguments(s.val1,argdict),replacearguments(s.val2,argdict),s.lineno)
	elif isinstance(s,Alias):
		for id in s.dict:
			if id in argdict:
				print_error("%s already used as function argument"%id,s.lineno)
				return None
		return Alias(s.dict,replacearguments(s.statement,argdict),s.lineno)
	elif isinstance(s,Var):
		newdecl=[]
		for cdecl in s.decl:
			if cdecl.id in argdict:
				print_error("%s already used as function argument"%s.decl.id,s.lineno)
				return None
			else:
				newdecl+=[Declaration(cdecl.id,replacearguments(cdecl.val,argdict),s.lineno)]
		return Var(newdecl,s.lineno)
	elif isinstance(s,IfWhile):
		return IfWhile(s.type,replacearguments(s.pred,argdict),replacearguments(s.statement,argdict),s.lineno)
	elif isinstance(s,IfElse):
		return IfElse(s.type,replacearguments(s.pred,argdict),replacearguments(s.statementif,argdict),replacearguments(s.statementelse,argdict),s.lineno)
	elif isinstance(s,RegStore):
		return RegStore([replacearguments(x,argdict) for x in s.storeset],replacearguments(s.statement,argdict),s.lineno)
	elif isinstance(s,Return):
		if "$ret" in argdict:
			return [OpExpression("=",argdict["$ret"],s.expr,s.lineno),Statement("GNZ",1,retcodelabel.id,s.lineno)]
		else:
			if isinstance(s.expr,int) or isinstance(s.expr,Register) or isinstance(s.expr,str):
				return []
			else:
				return s.expr
	elif isinstance(s,ArrayAccess):
		return ArrayAccess(replacearguments(s.id),s.index)
	elif s is None:
		return None
	else:
		print_critical_error("Unknown AST type (%s)"%s.__class__.__name__,s.lineno)
		return None

def expandfunctioncall(exp,storeret):
	global retcodelabel
	if exp.name in funcs:
		nfunc=funcs[exp.name]
		if len(exp.args)<len(nfunc.args):
			print_error("Too few arguments to %s (defined at line %d)"%(exp.name,nfunc.lineno),exp.lineno)
		elif len(exp.args)>len(nfunc.args):
			print_error("Too many arguments to %s (defined at line %d)"%(exp.name,nfunc.lineno),exp.lineno)
		else:
			nvar=getsysvar()
			argdict={}
			newstatementlist=[]
			if storeret:
				newstatementlist+=[Var([Declaration(nvar,None,exp.lineno)],exp.lineno)]
				argdict["$ret"]=nvar
			for i in range(len(nfunc.args)):
				prevs,cval=expandexpression(exp.args[i])
				newstatementlist+=prevs
				argdict[nfunc.args[i]]=cval
			retcodelabel=getsyscodelabel(exp.lineno)
			return newstatementlist+[replacearguments(nfunc.statement,argdict),retcodelabel],nvar
	else:
		print_error("Undefined function %s"%exp.name,exp.lineno)
		return [],None

def expandexpression(exp):
	global retcodelabel
	exp=simplifyexpression(exp)
	if isinstance(exp,OpExpression):
		if exp.op in unexpops:
			prevs,cval=expandexpression(exp.op1)
			if isinstance(cval,int) and exp.op in modifyexpops:
				print_error("Cannot modify integer literal %d with operator %s"%(cval,exp.op),exp.lineno)
				return [],None
			elif isinstance(cval,ArrayAccess) and exp.op in modifyexpops:
				print_error("Cannot modify array access with operator %s"%(exp.op),exp.lineno)
				return [],None
			elif cval is None:
				return [],None
			elif isinstance(cval,int):
				if exp.op=="!":
					if cval==0:
						return prevs,1
					else:
						return prevs,0
				else:
					print_critical_error("Unknown operator: %s"%exp.op,exp.lineno)
					return [],None
			elif isinstance(cval,str) or isinstance(cval,Register) or isinstance(cval,TempVar) or isinstance(cval,ArrayAccess):
				if exp.op in modifyexpops:
					return prevs+[Statement(expoptoop[exp.op],cval,0,exp.lineno)],cval
				else:
					if exp.op=="!":
						nvar=TempVar(getsysvar())
						return prevs+[Var([Declaration(nvar,0,exp.lineno)],exp.lineno),
									IfWhile("ifz",cval,
										Statement("MOV",nvar,1,exp.lineno),
									exp.lineno)],nvar
					else:
						if not isinstance(cval,TempVar):
							nvar=TempVar(getsysvar())
							prevs+=[Statement("MOV",nvar,cval,exp.lineno)]
							cval=nvar
						return prevs+[Statement(expoptoop[exp.op],cval,0,exp.lineno)],cval
			else:
				print_critical_error("Unknown expression type: %s"%cval.__class__.__name__,exp.lineno)
				return [],None
		else:
			prevs1,cval1=expandexpression(exp.op1)
			prevs2,cval2=expandexpression(exp.op2)
			if isinstance(cval1,int) and isinstance(cval2,int):
				if exp.op in modifyexpops:
					print_error("Cannot modify integer literal %d with operator %s",(cval1,exp.op))
				else:
					if exp.op=="+":
						newval=cval1+cval2
					elif exp.op=="-":
						newval=cval1-cval2
					elif exp.op=="&":
						newval=cval1&cval2
					elif exp.op=="|":
						newval=cval1|cval2
					elif exp.op=="~&":
						newval=(~cval1)&cval2
					elif exp.op=="^":
						newval=cval1^cval2
					elif exp.op=="<<":
						if cval2>=29:
							print_warning("Left shift with large constant %d"%cval2,exp.lineno)
							newval=0
						else:
							newval=cval1<<cval2
					elif exp.op==">>":
						if cval2<=-29:
							print_warning("Right shift with large negative constant %d"%cval2,exp.lineno)
							newval=0
						else:
							newval=cval1>>cval2
					else:
						print_critical_error("Unknown operator: %s"%exp.op,exp.lineno)
						return [],None
					if newval<-ARG_LIMIT or newval>=ARG_LIMIT:
						nvar=TempVar(getsysvar())
						return [Var([Declaration(nvar,None,exp.lineno)],exp.lineno),
								Statement("MOV",nvar,cval1,exp.lineno),
								Statement(expoptoop[exp.op],nvar,cval2,exp.lineno)],nvar
					else:
						return [],newval
			elif cval1 is None or cval2 is None:
				return [],None
			else:
				if not isinstance(cval1,TempVar) and exp.op not in modifyexpops:
					if exp.op in commutativeops and isinstance(cval2,TempVar):
						tempprevs,tempval=prevs1,cval1
						prevs1,cval1=prevs2,cval2
						prevs2,cval2=tempprevs,tempval
					else:
						nvar=TempVar(getsysvar())
						prevs1+=[Var([Declaration(nvar,None,exp.lineno)],exp.lineno),
								Statement("MOV",nvar,cval1,exp.lineno)]
						cval1=nvar
				if isinstance(cval1,int) and exp.op in modifyexpops:
					print_error("Cannot modify integer literal %d with operator %s"%(cval1,exp.op),exp.lineno)
					return [],None
				elif isinstance(cval1,ArrayAccess) and exp.op in modifyexpops:
					print_error("Cannot modify array access with operator %s"%(exp.op),exp.lineno)
					return [],None
				prevs=prevs1+prevs2
				if exp.op in compexpops and not exp.op=="~=":
					if exp.op=="<":
						return prevs+[Statement("SUB",cval1,cval2,exp.lineno),
											IfWhile("ifnn",cval1,
												Statement("MOV",cval1,0,exp.lineno),
											exp.lineno)],cval1
					else:
						print_critical_error("Unknown operator: %s"%exp.op,exp.lineno)
						return [],None
				elif exp.op in boolops:
					if exp.op=="&&":
						return prevs1+[IfWhile("if",cval1,
										[prevs2,
										IfWhile("ifz",cval2,
											Statement("MOV",cval1,0,exp.lineno),
										exp.lineno)],exp.lineno)],cval1
					elif exp.op=="||":
						return prevs1+[IfWhile("ifz",cval1,
										[prevs2,
										IfWhile("if",cval2,
											Statement("MOV",cval1,1,exp.lineno),
										exp.lineno)],exp.lineno)],cval1
					else:
						print_critical_error("Unknown operator: %s"%exp.op,exp.lineno)
						return [],None
				else:
					if exp.op in modifyexpops and isinstance(cval1,TempVar):
						print_warning("Modification to temporary variable with operator %s"%exp.op,exp.lineno)
						return prevs,cval1
					elif exp.op in modifyexpops and isinstance(cval1,int):
						print_error("Cannot modify integer literal %d with operator %s",(cval1,exp.op))
						return [],None
					else:
						return prevs+[Statement(expoptoop[exp.op],cval1,cval2,exp.lineno)],cval1
	elif isinstance(exp,FunctionCall):
		return expandfunctioncall(exp,True)
	elif isinstance(exp,int) or isinstance(exp,Register) or isinstance(exp,TempVar) or isinstance(exp,ArrayAccess) or isinstance(exp,str):
		if isinstance(exp,int):
			if exp<-ARG_LIMIT or exp>=ARG_LIMIT:
				ok,newexp=checkintbounds(exp,-1)
				cdata=getsysdata(-1,newexp)
				nvar=getsysvar()
				# print_error("Integer literal %d out of range [-256,256)"%exp,lineno)
				return [Var([Declaration(nvar,None,-1)],-1),
						Statement("LOAD",nvar,cdata,-1)
						],nvar
			else:
				return [],exp
		elif isinstance(exp,str) and exp in defines:
			return [],defines[exp]
		else:
			return [],exp

def replaceidentifiers(s):
	global numastnodes
	global variables
	global breaks
	global continues
	global codelabelset
	if isinstance(s,list):
		newstatementlist=[]
		clistid=numastnodes
		numastnodes+=1
		newvariables=set()
		for cstatement in s:
			if isinstance(cstatement,Var):
				for cdecl in cstatement.decl:
					if isinstance(cdecl.id,TempVar):
						cdecl=cdecl._replace(id=cdecl.id.id)
					if cdecl.id in assigned:
						print_error("Identifier %s already defined in line %d"%(cdecl.id,assigned[cdecl.id]),cstatement.lineno)
					else:
						newvariables|={cdecl.id}
						variables|={cdecl.id}
						usagecnt[touniquevarname(cdecl.id)]=0
						assigned[cdecl.id]=cstatement.lineno
						newstatementlist+=[Var(touniquevarname(cdecl.id),cstatement.lineno)]
						if cdecl.val is not None:
							newstatementlist+=[replaceidentifiers(OpExpression("=",cdecl.id,cdecl.val,cstatement.lineno))]
			else:
				nextstatement=replaceidentifiers(cstatement)
				if nextstatement is not None:
					newstatementlist+=[nextstatement]
		for cvar in newvariables:
			variables.remove(cvar)
			assigned.pop(cvar)
			incrementvarnamecnt(cvar)
		if len(newstatementlist)==0:
			return None
		else:
			return StatementList(clistid,False,newstatementlist,-1)
	elif isinstance(s,Statement):
		isvalid=True
		if isinstance(s.val1,TempVar):
			s=s._replace(val1=s.val1.id)
		if isinstance(s.val2,TempVar):
			s=s._replace(val2=s.val2.id)
		if isinstance(s.cmd,str):
			if s.cmd in gotobinops and not (isinstance(s.val2,str) and s.val2 in codelabelset):
				print_warning("Code label not used in goto command: %s"%s.val2,s.lineno)
		cvalid,translateret=translateval(s.val1,s.lineno)
		if cvalid:
			s=s._replace(val1=translateret)
		else:
			isvalid=False
		cvalid,translateret=translateval(s.val2,s.lineno)
		if cvalid:
			s=s._replace(val2=translateret)
		else:
			isvalid=False
		if isinstance(s.val1,str) and s.val1 in variables:
			newval1=touniquevarname(s.val1)
			usagecnt[newval1]+=1
			if s.cmd!="MOV" and s.cmd!="LOAD":
				usagecnt[newval1]+=1
			s=s._replace(val1=newval1)
		if isinstance(s.val2,str) and s.val2 in variables:
			newval2=touniquevarname(s.val2)
			usagecnt[newval2]+=1;
			s=s._replace(val2=newval2)
		if s.cmd in binopswithregstore and not (isinstance(s.val1,Register) or (isinstance(s.val1,str) and s.val1 in usagecnt)):
			print_error("Operator %s requires first argument to be a register"%s.cmd,s.lineno)
			isvalid=False
		if s.cmd in unopswithregstore and not (isinstance(s.val1,Register) or (isinstance(s.val1,str) and s.val1 in usagecnt)):
			print_error("Operator %s requires argument to be a register"%s.cmd,s.lineno)
			isvalid=False
		if s.cmd=="ADD" and s.val2==1:
			s=Statement("INC",s.val1,0,s.lineno)
		if s.cmd=="SUB" and s.val2==1:
			s=Statement("DEC",s.val1,0,s.lineno)
		if isvalid:
			return s
		else:
			return None
	elif isinstance(s,DeviceStatement):
		devid=None
		if isinstance(s.devid,str):
			if s.devid in defines:
				devid=defines[s.devid]
				if not isinstance(devid,int):
					print_error("Device identifier must be an integer",s.lineno)
					devid=None
			else:
				print_error("Undefined device identifier %s"%s.devid,s.lineno)
		elif isinstance(s.devid,int):
			devid=s.devid
		else:
			print_error("%s cannot be a device identifier"%s.devid.__class__.__name__,s.lineno)
		if isinstance(devid,int):
			if devid<0 or devid>=16:
				print_error("Device identifier %d not within the range [0,16) (only 16 devices allowed)"%devid,s.lineno)
				return None
			else:
				return replaceidentifiers(Statement("DEV"+str(devid),s.val1,s.val2,s.lineno))
		else:
			return None
	elif isinstance(s,CodeLabel):
		return s
	elif isinstance(s,Alias):
		isvalid=True
		for id in s.dict:
			if id in assigned:
				print_error("Identifier %s already defined in line %d"%(id,assigned[id]),s.lineno)
				isvalid=False
		if isvalid:
			for id,reg in s.dict.items():
				defines[id]=reg
				assigned[id]=s.lineno
			res=replaceidentifiers(s.statement)
			for id in s.dict:
				defines.pop(id)
				assigned.pop(id)
			return res
		else:
			return None
	elif isinstance(s,Define):
		return None
	elif isinstance(s,Data):
		return None
	elif isinstance(s,Var):
		print_error("Variable %s defined outside statement list"%s.decl[0].id,s.lineno)
		return None
	elif isinstance(s,IfWhile):
		if isinstance(s.pred,str) and s.pred in reldatapointers:
			print_warning("Data pointer %s used as predicate"%s.pred,s.lineno)
		nextsyscodelabel=getsyscodelabel(s.lineno)
		if s.type[0:2]=="do":
			outsyscodelabel=getsyscodelabel(s.lineno)
			continues+=[nextsyscodelabel.id]
			breaks+=[outsyscodelabel.id]
			codelabelset|={nextsyscodelabel.id,outsyscodelabel.id}
			assigned[nextsyscodelabel.id]=s.lineno
			assigned[outsyscodelabel.id]=s.lineno
			prevs,cval=expandexpression(s.pred)
			if s.type[2:]=="while":
				res=replaceidentifiers([nextsyscodelabel,
										s.statement]+prevs+[
										Statement("GNZ",cval,nextsyscodelabel.id,s.lineno),
										outsyscodelabel])
			elif s.type[2:]=="whilen":
				res=replaceidentifiers([nextsyscodelabel,
										s.statement]+prevs+[
										Statement("GN",cval,nextsyscodelabel.id,s.lineno),
										outsyscodelabel])
			continues.pop()
			breaks.pop()
			if isinstance(res,StatementList):
				res=res._replace(isloop=True)
			return res
		elif s.type[0:2]=="if":
			nextsyscodelabel=getsyscodelabel(s.lineno)
			if s.type=="if":
				if isinstance(s,OpExpression) and s.pred.op=="==":
					return replaceidentifiers(IfWhile("ifz",OpExpression("~=",s.pred.op1,s.pred.op2,s.lineno),s.lineno))
				else:
					return replaceidentifiers(IfElse("ifz",s.pred,None,s.statement,s.lineno))
			elif s.type[2:]=="z":
				prevs,cval=expandexpression(s.pred)
				return replaceidentifiers(prevs+[Statement("GNZ",cval,nextsyscodelabel.id,s.lineno),
												s.statement,
												nextsyscodelabel])
			elif s.type[2:]=="nn":
				prevs,cval=expandexpression(s.pred)
				return replaceidentifiers(prevs+[Statement("GN",cval,nextsyscodelabel.id,s.lineno),
												s.statement,
												nextsyscodelabel])
	elif isinstance(s,IfElse):
		if s.type=="if":
			return replaceidentifiers(IfElse("ifz",s.pred,s.statementelse,s.statementif,s.lineno))
		else:
			if isinstance(s.pred,str) and s.pred in reldatapointers:
				print_warning("Data pointer %s used as predicate"%s.pred,s.lineno)
			ifcodelabel=getsyscodelabel(s.lineno)
			elsecodelabel=getsyscodelabel(s.lineno)
			prevs,cval=expandexpression(s.pred)
			if s.type=="ifz":
				return replaceidentifiers(prevs+[Statement("GNZ",cval,elsecodelabel.id,s.lineno),
												s.statementif,
												Statement("GNZ",1,ifcodelabel.id,s.lineno),
												elsecodelabel,
												s.statementelse,
												ifcodelabel])
			elif s.type=="ifnn":
				return replaceidentifiers(prevs+[Statement("GN",cval,elsecodelabel.id,s.lineno),
												s.statementif,
												Statement("GNZ",1,ifcodelabel.id,s.lineno),
												elsecodelabel,
												s.statementelse,
												ifcodelabel])
	elif isinstance(s,RegStore):
		dataids=[]
		resstatementfront=[]
		resstatementback=[]
		for cid in s.storeset:
			if isinstance(cid,Register):
				cdata=getsysdata(s.lineno)
				resstatementfront+=[Statement("STORE",cdata,cid,s.lineno)]
				resstatementback+=[Statement("LOAD",cid,cdata,s.lineno)]
		resstatementback.reverse()
		finalstatement=resstatementfront+[s.statement]+resstatementback
		return replaceidentifiers(finalstatement)
	elif isinstance(s,OpExpression):
		newstatements,cval=expandexpression(s)
		return replaceidentifiers(newstatements)
	elif isinstance(s,FunctionCall):
		newstatements,cval=expandfunctioncall(s,False)
		return replaceidentifiers(newstatements)
	elif isinstance(s,BreakCont):
		if s.type=="continue":
			if s.val<=0 or s.val>len(continues):
				print_error("Invalid argument %d"%s.val,s.lineno)
			return replaceidentifiers(Statement("GNZ",1,continues[-s.val],s.lineno))
		elif s.type=="break":
			if s.val<=0 or s.val>len(breaks):
				print_error("Invalid argument %d"%s.val,s.lineno)
			return replaceidentifiers(Statement("GNZ",1,breaks[-s.val],s.lineno))
			print_critical_error("Unknown command (%s)"%s,s.lineno)
			return None
	elif isinstance(s,Function):
		return None
	elif isinstance(s,Return):
		print_error("Return statement in main body",s.lineno)
		return None
	elif isinstance(s,Register):
		print_warning("Register r%d used as statement"%s.val,-1)
		return None
	elif isinstance(s,int):
		print_warning("Integer constant %d used as statement"%s,-1)
		return None
	elif isinstance(s,str):
		print_warning("Identifier %s used as statement"%s,-1)
		return None
	elif s is None:
		return None
	else:
		print_critical_error("Unknown AST type (%s)"%s.__class__.__name__,s.lineno)
		return None

def checkintbounds(val,lineno):
	if val<-0x10000000 or val>=0x20000000:
		print_warning("Integer literal out of range [-0x10000000,0x20000000): %d"%val,lineno)
	return True,(val&DATA_MASK)|INTEGER_MASK

def preprocess(s):
	global codelabelset
	global datainit
	global cfunc
	if isinstance(s,list):
		for cstatement in s:
			preprocess(cstatement)
	elif isinstance(s,Alias) or isinstance(s,IfWhile):
		preprocess(s.statement)
	elif isinstance(s,IfElse):
		preprocess(s.statementif)
		preprocess(s.statementelse)
	elif isinstance(s,Data):
		if s.id in assigned:
			print_error("Identifier %s already defined in line %d"%(s.id,assigned[s.id]),s.lineno)
		else:
			reldatapointers[s.id]=len(datainit)
			if isinstance(s.val,list):
				processedval=[]
				ok=True
				for cval in s.val:
					cok,checkres=checkintbounds(cval,s.lineno)
					if cok:
						processedval+=[checkres]
					else:
						ok=False
						break
				if ok:
					datainit+=processedval
			else:
				ok,checkres=checkintbounds(s.val,s.lineno)
				if ok:
					datainit+=[checkres]
			assigned[s.id]=s.lineno
	elif isinstance(s,Define):
		if s.id in assigned:
			print_error("Identifier %s already defined in line %d"%s.id,assigned[s.id])
		else:
			defines[s.id]=s.val
			assigned[s.id]=s.lineno
	elif isinstance(s,RegStore):
		preprocess(s.statement)
	elif isinstance(s,CodeLabel):
		if cfunc!="$":
			print_warning("Code label %s in function body"%s.id)
		if s.id in assigned:
			if s.id in codelabelset:
				print_warning("Code label %s already defined in line %d"%(s.id,assigned[s.id]),s.lineno)
			else:
				print_error("Identifier %s already defined in line %d"%s.id,assigned[s.id])
		else:
			codelabelset|={s.id}
			assigned[s.id]=s.lineno
	elif isinstance(s,Function):
		if cfunc=="$":
			newvariables=set()
			cfunc=s.name
			preprocess(s.statement)
			cfunc="$"
			funcs[s.name]=Function(s.name,s.args,s.statement,s.lineno)
		else:
			print_error("Cannot define function %s in function %s"%(s.name,cfunc),s.lineno)

def localoptimise():
	global unravelledstatements
	newindices=[]
	for i in range(len(unravelledstatements)):
		if (unravelledstatements[i].cmd=="GNZ" or unravelledstatements[i].cmd=="GN"):
			if isinstance(unravelledstatements[i].val2,str) and unravelledstatements[i].val2 in codelabels:
				if codelabels[unravelledstatements[i].val2]==i+1:
					unravelledstatements[i]=None
		if i==0:
			newindices+=[0]
		else:
			if unravelledstatements[i] is None:
				newindices+=[newindices[i-1]]
			else:
				newindices+=[newindices[i-1]+1]
	newindices+=[newindices[-1]+1]
	for ccodelabel in codelabels:
		codelabels[ccodelabel]=newindices[codelabels[ccodelabel]]
	unravelledstatements=[x for x in unravelledstatements if x is not None]

if __name__=="__main__":
	if len(sys.argv)!=1 and len(sys.argv)!=3:
		print("Please call assembler.py in the following format:")
		print("assembler.py <input file> <output file>")
	else:
		if len(sys.argv)==3:
			inputfilename=sys.argv[1]
			outputfilename=sys.argv[2]
		elif len(sys.argv)==1:
			inputfilename=input("Enter input file: ")
			outputfilename=input("Enter output file: ")
		inputfile=open(inputfilename,"r")
		global code
		code=inputfile.read()
		global outputfile
		outputfile=open(outputfilename,"w")
		global intfile
		intfile=open("assembly_intermediate.ac","w")
		lexer=lex.lex()
		yacc.yacc()
		statementlist=yacc.parse(code)
		if statementlist is None:
			print_warning("Assembly code file is empty.",0);
		else:
			preprocess(statementlist)
			statementlist=replaceidentifiers(statementlist)
			fregassigns=allocateregisters(statementlist)
			for i in range(len(fregassigns)):
				assignreg(Register(i),fregassigns[i].assigns)
			unravelstructure(statementlist)
			localoptimise();
			if len(unravelledstatements)>0:
				if unravelledstatements[-1].cmd!="SHUTDOWN":
					unravelledstatements+=[Statement("SHUTDOWN",0,0,-1)]
				for cstatement in unravelledstatements:
					emitstatement(cstatement)
				for cdata in datainit:
					outputfile.write("%08x\n"%cdata)
				if len(unravelledstatements)+len(datainit)>512:
					print("Warning: Memory used exceeds 512 word limit (%d words)"%(len(unravelledstatements)+len(datainit)))
			if numerrors==0:
				print("Assembly complete: %d instructions, %d words of data (%d total)."%(len(unravelledstatements),len(datainit),len(unravelledstatements)+len(datainit)))
			else:
				print("Assembly failed: %d error(s) detected."%numerrors)
