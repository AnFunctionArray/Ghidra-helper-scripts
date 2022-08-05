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

public class CreateStructure extends GhidraScript {
	
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
		for (Function fn : funcs)
		//Function fn = getFunctionAt(currentAddress);
		{
			println(fn.getName());
			Variable[] allvars = fn.getLocalVariables();
			boolean inited = false;
			DecompileResults res = decomp.decompileFunction(fn, 10000, monitor);
			
			HighFunction hifun = res.getHighFunction();
			
			if(hifun == null) continue;
			
			Iterator<HighSymbol> syms = hifun.getLocalSymbolMap().getSymbols();
			
			//StructureDataType dt = new StructureDataType(new CategoryPath(DEFAULT_CATEGORY), fn.getName() + "_" + currentAddress + "_stack_struct",
					//		size, f.getProgram().getDataTypeManager());
			
			long minoffset = Integer.MAX_VALUE;
			long maxoffset = Integer.MIN_VALUE;
			HighVariable deepesthivar = null;
			
			//determine min offset to calculate structure size
			//and variable to populate
			Map<Integer,HighSymbol> symssorted = new TreeMap<>();
			
			while(syms.hasNext()) {
				HighSymbol next = syms.next();
				HighVariable hivar = next.getHighVariable();
				if(hivar == null) continue;
				Varnode node = hivar.getRepresentative();
				if(node.isAddrTied()) {
					println(""+node.getAddress().getOffset());
					if(minoffset > node.getAddress().getOffset()) {
						minoffset = node.getAddress().getOffset();
						deepesthivar = hivar;
					}
					if(maxoffset < node.getAddress().getOffset()) {
						maxoffset = node.getAddress().getOffset();
					}
					symssorted.put((int)node.getAddress().getOffset(), next);	
				}
			}
			
			if(deepesthivar == null) continue;
			
			try {
			
			Structure struc = createNewStruct(deepesthivar, 0, fn, false);
			
			//syms = hifun.getLocalSymbolMap().getSymbols();
			
			Iterator<Entry<Integer,HighSymbol>> mapiter = symssorted.entrySet().iterator() ;
			
			//populate fields
			
			while(mapiter.hasNext()) {
				Entry<Integer,HighSymbol> en = mapiter.next();
				HighSymbol next = en.getValue();
				HighVariable hivar = next.getHighVariable();
				if(hivar == null) continue;
				Varnode node = hivar.getRepresentative();
				if(node.isAddrTied()) {
					long offset = Math.abs(node.getAddress().getOffset() - minoffset);
					println("at " + offset);
					struc.insertAtOffset((int)offset, hivar.getDataType(), 0, hivar.getName(), "");
				}
			}
			
			
			
			HighFunctionDBUtil.updateDBVariable(deepesthivar.getSymbol(), null, struc,
					SourceType.USER_DEFINED);
			}
			catch(Exception exc) {
				println(exc.toString());
			}
			
			//StructureDataType dt = new StructureDataType(new CategoryPath(DEFAULT_CATEGORY), fn.getName() + "_" + currentAddress + "_stack_struct",
			//		size, f.getProgram().getDataTypeManager());
			
			//for(Variable var : allvars) {
				//println(frame.getLocals()[0].getMinAddress().toString());
				//Address curr = getAddressFactory().getAddress("Stack[0x0]");//frame.getLocals()[0].getMinAddress();
				//curr.add(frame.getFrameSize());
				//println(curr.toString());
				/*Iterator<VarnodeAST> iter = hifun.locRange();
				
				while(iter.hasNext()) {
					VarnodeAST next = iter.next();
					if(next.isAddrTied()) {
						HighVariable hivar = next.getHigh();
						if(!hivar.getSymbol().isGlobal()) {
							
						}
					}
					println(next.toString());
				}
			//}
			
	        
	        //println("type : " + dattyp.getCategoryPath().getName());
	        
	        /*ClangTokenGroup tokengrp = res.getCCodeMarkup();
	        
	        if(tokengrp == null) return;
	        
	        ClangToken tokeres = null;
	        
	        //println("searching for " + datatypstring);
	        
	        mainloop:
	        for(ClangNode  token : tokengrp) {
	        	if(token instanceof ClangFuncProto) {
	        		/*for(ClangNode  outter : ((ClangFuncProto)token)) {
	        			if(outter instanceof ClangVariableDecl)
	        			for(ClangNode inner2 : ((ClangVariableDecl)outter)) {
		        			if(inner2 instanceof ClangToken) {
		        				if(((ClangToken)inner2).getText().equals(datatypstring)) {
					        		tokeres = (ClangToken)inner2;
					        		//println(inner2.getClass().toString());
					        		break mainloop;
					        	}
			        			else {
			        				//println("" + ((ClangToken)inner2).getText());
			        			}
		        			}
		        			else {
		        				//println(inner2.getClass().toString());
		        			}
	        			}*/
	        	/*}
	        	else {
	        		println(token.getClass().toString());
	        	}
	        }
	        //if(tokeres == null) continue;
	        //println("found");
	        
			//ClangToken tokeres = new ClangToken(null, datatypstring);
			/*DecompilerLocation loc = new DecompilerLocation(currentProgram, fn.getEntryPoint(), fn.getEntryPoint(), res, tokeres,1,1);
			println("" + loc);
			FillOutStructureCmd fillCmd =
					new FillOutStructureCmd(currentProgram, loc, state.getTool());
			fillCmd.applyTo(currentProgram, this.monitor);*/

			//break;
		}
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