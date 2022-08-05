/* ###
 * IP: GHIDRA
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 * 
 *      http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
// Automatically creates a structure definition based on the references seen to the structure
//   To use this, place the cursor on a function parameter for example func(int *this),
//   (for a C++ this call function)
//   This script will automatically create a structure definition for the pointed at structure
//   and fill it out based on the references found by the decompiler.
//
//   If the parameter is already a structure pointer, any new references found will be added
//   to the structure, even if the structure must grow.
//
//   Eventually this WILL be put into a global type analyzer, but for now it is most useful.
//
//   This script assumes good flow, that switch stmts are good.
//
//   This script CAN be used in the decompiler by assigning a Binding a Keyboard key to it, then
//   placing the cursor on the variable in the decompiler that is a structure pointer (even if it
//   isn't one now, and then pressing the Quick key.
//
//@category Data Types
//@keybinding F6

import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.TreeMap;
import java.util.Map.Entry;

import docking.ActionContext;
import docking.action.KeyBindingData;
import docking.action.MenuData;
import docking.widgets.textfield.IntegerTextField;
import ghidra.app.cmd.label.RenameLabelCmd;
import ghidra.app.context.ListingActionContext;
import ghidra.app.decompiler.*;
import ghidra.app.decompiler.component.DecompilerController;
import ghidra.app.plugin.core.decompile.DecompilerActionContext;
import ghidra.app.plugin.core.decompile.actions.CreateStructureVariableAction;
import ghidra.app.plugin.core.decompile.actions.FillOutStructureCmd;
import ghidra.app.plugin.core.decompile.actions.FillOutStructureCmd.OffsetPcodeOpPair;
import ghidra.app.script.GhidraScript;
import ghidra.app.util.HelpTopics;
import ghidra.framework.model.DomainObject;
import ghidra.framework.options.*;
import ghidra.framework.plugintool.PluginTool;
import ghidra.framework.plugintool.util.*;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSet;
import ghidra.program.model.data.*;
import ghidra.program.model.lang.PrototypeModel;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.pcode.HighFunction;
import ghidra.program.model.pcode.HighFunctionDBUtil;
import ghidra.program.model.pcode.HighParam;
import ghidra.program.model.pcode.HighSymbol;
import ghidra.program.model.pcode.HighVariable;
import ghidra.program.model.pcode.PcodeException;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.Varnode;
import ghidra.program.model.pcode.VarnodeAST;
import ghidra.program.model.symbol.Namespace;
import ghidra.program.model.symbol.SourceType;
import ghidra.program.model.symbol.Symbol;
import ghidra.program.model.symbol.SymbolTable;
import ghidra.program.util.FunctionParameterFieldLocation;
import ghidra.program.util.ProgramLocation;
import ghidra.program.util.VariableLocation;
import ghidra.util.HelpLocation;
import ghidra.util.Msg;
import ghidra.util.exception.AssertException;
import ghidra.util.exception.DuplicateNameException;
import ghidra.util.exception.InvalidInputException;
import ghidra.util.task.TaskMonitor;

public class ExtractDataInGAS extends GhidraScript {
	
	DecompInterface decomp;
	private PluginTool tool;

	@Override
	public void run() throws Exception {
		/*println("" + currentLocation.toString());
		FillOutStructureCmd fillCmd =
				new FillOutStructureCmd(currentProgram, currentLocation, state.getTool());
		fillCmd.applyTo(currentProgram, this.monitor);*/
		FunctionIterator funcs = currentProgram.getFunctionManager().getFunctions(true);
		tool = state.getTool();
		decomp = setUpDecompiler(currentProgram);
		MemoryBlock memblk = getCurrentProgram().getMemory().getBlock("__data");
		
		println(memblk.getStart() + " - " + memblk.getEnd());
		
		Address beg = memblk.getStart(), last = beg;
		
		String asmrepall = "", crepall = "", asmrep = "", crep = "";
		
		//int solitaren = 0;
		
		File dir = askDirectory ( "Select Out Dir", "OK" );
		if ( dir == null ) {
			printerr( "No file selected, ending script." );
			return;
		}
		
		Data at = null;
		
		while(beg.getOffset() < memblk.getEnd().getOffset()) {
			//if(at != null) {
				if (getSymbolAt(last) != null) {
					asmrepall += asmrep + "\n";
					crepall += crep + "\n";
				}
				else {
					asmrepall += asmrep.substring(2) + "\n";
				}
			//}
			Msg.info(this, asmrep);
			Msg.info(this, crep);
			at = getDataAt(beg);
			
			String datname = getSymbolAt(beg) != null ? getSymbolAt(beg).getName() 
					: "";	
			
			datname = datname.replaceAll("(?!_[0-9])\\W", "_");
			
			last = beg;
			//beg = getDataAfter(at).getAddress();
			
			String val;
			
			DataType type;
			
			Class<? extends DataType> typeclass;
			
			if(at == null) {
				val = "0" + String.format("%02X", getByte(last)) + "h";
				type = new CharDataType();
				typeclass = type.getClass();
			}
			else {
				type = at.getBaseDataType();
				typeclass = type.getClass();
				val = typeclass == PointerDataType.class ? getSymbolAt(((Address)at.getValue())).getName()
						: at.getDefaultValueRepresentation();
			}
			
			Msg.info(this, type.getLength());
			beg = beg.add(typeclass == StringDataType.class ? ((StringDataType)type).getLength(at, -1) : type.getLength());

			
			if(typeclass == StringDataType.class) {
				StringDataType strtyp = (StringDataType)type;
				
				crep = "char " + datname + "[1];";
				asmrep = datname + ": .asciz " + val;
				continue;
			}
			else if(typeclass == CharDataType.class) {
				crep = "char " + datname + ";";
				asmrep = datname + ": .byte " + val;
				continue;
			}
			else if(typeclass == PointerDataType.class) {
				crep = "void *" + datname + ";";
				asmrep = datname + ": .word " + val;
				continue;
			}
			
			boolean issigned = typeclass == AbstractIntegerDataType.class ? ((AbstractIntegerDataType)type).isSigned() : false;
			String cprefix = issigned ? "" : "unsigned ";
			
			switch(type.getLength()) {
			case 1:
				crep = cprefix + "char " + datname + ";";
				asmrep = datname + ": .byte " + val;
				continue;
			case 2:
				crep = cprefix + "short " + datname + ";";
				asmrep = datname + ": .hword " + val;
				continue;
			case 4:
				if(typeclass != AbstractFloatDataType.class) {
					crep = cprefix + "int " + datname + ";";
					asmrep = datname + ": .long " + val;
				}
				else {
					crep = cprefix + "float " + datname + ";";
					asmrep = datname + ": .float " + val;
				}
				continue;
			case 8:
				if(typeclass != AbstractFloatDataType.class) {
					crep = cprefix + "long long " + datname + ";";
					asmrep = datname + ": .quad " + val;
				}
				else {
					crep = cprefix + "double " + datname + ";";
					asmrep = datname + ": .float " + val;
				}
				continue;
			}
			
			Msg.error(this, "Error data type is not handled " + type.toString());
			break;
		}
		
		
		
		Files.writeString(Path.of(dir.getPath() + "/out.c"), crepall);
		Files.writeString(Path.of(dir.getPath() + "/asmrep.s"), asmrepall);
	}
	
	private Namespace createUniqueClassName(Namespace rootNamespace) {
		SymbolTable symbolTable = currentProgram.getSymbolTable();
		String newClassBase = "AutoClass";
		String newClassName = "";
		for (int i = 1; i < 1000; ++i) {
			newClassName = newClassBase + Integer.toString(i);
			if (symbolTable.getSymbols(newClassName, rootNamespace).isEmpty()) {
				break;
			}
		}
		// Create the class
		GhidraClass newClass = null;
		try {
			newClass =
				symbolTable.createClass(rootNamespace, newClassName, SourceType.USER_DEFINED);
		}
		catch (DuplicateNameException e) {
			Msg.error(this, "Error creating class '" + newClassName + "'", e);
		}
		catch (InvalidInputException e) {
			Msg.error(this, "Error creating class '" + newClassName + "'", e);
		}
		return newClass;
	}

	private String createUniqueStructName(HighVariable var, String category, String base) {
		return currentProgram.getDataTypeManager().getUniqueName(new CategoryPath(category), base);
	}
	
	private static final String DEFAULT_BASENAME = "astruct";
	private static final String DEFAULT_CATEGORY = "/auto_structs";
	
	/**
	 * Create a new structure of a given size. If the associated variable is a 'this' pointer,
	 * make sure there is a the structure is associated with the class namespace.
	 * @param var is the associated variable
	 * @param size is the desired structure size
	 * @param f is the function owning the variable
	 * @param isThisParam is true if the variable is a 'this' variable
	 * @return the new Structure
	 */
	private Structure createNewStruct(HighVariable var, int size, Function f, boolean isThisParam) {
		if (isThisParam) {
			Namespace rootNamespace = currentProgram.getGlobalNamespace();
			Namespace newNamespace = createUniqueClassName(rootNamespace);
			String name = f.getName();
			Symbol symbol = f.getSymbol();
			RenameLabelCmd command =
				new RenameLabelCmd(symbol, name, newNamespace, SourceType.USER_DEFINED);
			if (!command.applyTo(currentProgram)) {
				return null;
			}
			Structure structDT = VariableUtilities.findOrCreateClassStruct(f);
// FIXME: How should an existing packed structure be handled? Growing and offset-based placement does not apply
			int len = structDT.isZeroLength() ? 0 : structDT.getLength();
			if (len < size) {
				structDT.growStructure(size - len);
			}
			return structDT;
		}
		String structName = createUniqueStructName(var, DEFAULT_CATEGORY, DEFAULT_BASENAME);

		StructureDataType dt = new StructureDataType(new CategoryPath(DEFAULT_CATEGORY), structName,
			size, f.getProgram().getDataTypeManager());
		return dt;
	}
	
	private DecompInterface setUpDecompiler(Program program) {
 		DecompInterface decompInterface = new DecompInterface();

 		// call it to get results
 		if (!decompInterface.openProgram(currentProgram)) {
 			println("Decompile Error: " + decompInterface.getLastMessage());
 			return null;
 		}

 		DecompileOptions options;
 		options = new DecompileOptions();
 		OptionsService service = state.getTool().getService(OptionsService.class);
 		if (service != null) {
 			ToolOptions opt = service.getOptions("Decompiler");
 			options.grabFromToolAndProgram(null, opt, program);
 		}
 		decompInterface.setOptions(options);

 		decompInterface.toggleCCode(true);
 		decompInterface.toggleSyntaxTree(true);
 		decompInterface.setSimplificationStyle("decompile");

 		return decompInterface;
 	}
}