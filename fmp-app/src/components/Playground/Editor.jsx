import { useState, useRef, useEffect} from 'react'
import Editor from "@monaco-editor/react";
import { MDBBtn } from 'mdb-react-ui-kit';
import Tools from './Tools';
import  {limbooleConf, limbooleLang } from '../../assets/languages/limboole'
import {smt2Conf, smt2Lang, smt2ComplitionProvider } from '../../assets/languages/smt2'
import { nuxmvConf, nuxmvLang } from '../../assets/languages/nuxmv'
import { alloyConf, alloyLang } from '../../assets/languages/alloy'



const CodeEditor = (props) => {
  const editorRef = useRef(null)


  function handleEditorDidMount(editor, monaco) {
    editorRef.current = editor
    editorRef.current.focus()
    // register limboole language
    monaco.languages.register({ id: 'limboole' })
    monaco.languages.setMonarchTokensProvider('limboole', limbooleLang)
    monaco.languages.setLanguageConfiguration('limboole', limbooleConf)
    
    // register smt2 language
    monaco.languages.register({ id: 'smt2' })
    monaco.languages.setMonarchTokensProvider('smt2', smt2Lang)
    monaco.languages.setLanguageConfiguration('smt2', smt2Conf)
    monaco.languages.registerCompletionItemProvider('smt2', smt2ComplitionProvider);
    
    // register nuxmv language
    monaco.languages.register({ id: 'xmv' })
    monaco.languages.setMonarchTokensProvider('xmv', nuxmvLang)
    monaco.languages.setLanguageConfiguration('xmv', nuxmvConf)
    
    // register alloy language
    monaco.languages.register({ id: 'als' })
    monaco.languages.setMonarchTokensProvider('als', alloyLang)
    monaco.languages.setLanguageConfiguration('als', alloyConf)

    // set limboole as default language
    monaco.editor.setModelLanguage(editor.getModel(), 'limboole');

  }

  function getEditorValue(value, event) {
    editorRef.current.getValue()
    console.log(editorRef.current.getValue())
    props.setEditorValue(editorRef.current.getValue())
  }

  function setEditorValue(value, event) {
    editorRef.current.setValue(value)
  }



  const handleCodeChange = (newCode) => {
    props.setEditorValue(newCode)
  }


  return (
    <>

      <div className="App">
        <Editor
          height="60vh"
          width="100%"
          language={props.language.id}
          defaultValue="# Write your code here"
          theme="vs-dark"
          options={{
            minimap: {
              enabled: false,
            },
            automaticLayout: true,
            mouseWheelZoom: true,
            bracketPairColorizationOptions: {
              enabled: true,
              independentColorPoolPerBracketType: true,
            },
          }}
          onMount={handleEditorDidMount}
          onChange={handleCodeChange}
        />

        {/* <MDBBtn className='me-1' color='success' onClick={() => handleLanguageChange('limboole')}>
          Limboole
        </MDBBtn>
        <MDBBtn className='me-1' color='success' onClick={() => handleLanguageChange('smt2')}>
          SMT
        </MDBBtn>
        <MDBBtn className='me-1' color='success' onClick={() => handleLanguageChange('xmv')}>
          XMV
        </MDBBtn>
        <MDBBtn className='me-1' color='success' onClick={() => handleLanguageChange('als')}>
          ALS
        </MDBBtn> */}
      </div>
    </>
  )
}

export default CodeEditor;
