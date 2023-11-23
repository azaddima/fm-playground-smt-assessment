import React, {useState, useRef} from 'react'
import Editor from './Editor.jsx'
import Output from './Output.jsx'
import Tools from './Tools.jsx'
import { FaUpload, FaDownload } from 'react-icons/fa'
import Select from 'react-select';
import { MDBBtn } from 'mdb-react-ui-kit';

import Options from '../../assets/config/AvailableTools.js'
import run_limboole from '../../assets/js/limboole'


const Playground = () => {
  const [editorValue, setEditorValue] = useState('')
  const [language, setLanguage] = useState(Options[1])

  const handleLanguageChange = (newLanguage) => {
    console.log(newLanguage)
    setLanguage(newLanguage)
  }

  
  const handleToolExecution = () => {
    if (language.value >= 0 && language.value < 3){
      run_limboole(window.Wrappers[language.value], editorValue)
    }else if (language.value == 3) {
      console.log('SMT will be executed')
    }else if (language.value == 4) {
      console.log('NuXmv will be executed')
    }else if (language.value == 5) {
      console.log('Alloy will be executed')
    }
  }

  return (
    <div className="container">
      <Tools 
        onChange={handleLanguageChange}
      />
      <div className="row">
        <div className="col-md-6">
          <div className='row'>
            <div className='col-md-4'>
              <h2>Input</h2>
            </div>
            <div className='col-md-8'>
              <div className='d-flex justify-content-end'>
                <div className='col-md-4'>
                  <Select />
                </div>
                <div className='col-md-2 btn btn-outline-dark'>
                  <FaUpload
                    role='button'
                  />
                </div>
                <div className='col-md-2 btn btn-outline-dark'>
                  <FaDownload />
                </div>
              </div>
            </div>
            <Editor 
              setEditorValue={setEditorValue}
              editorValue={editorValue}
              language={language}
              setLanguage={setLanguage}
            />
          </div>
        </div>
        <div className="col-md-6">
          <h2>Output</h2>
          <Output />
        </div>
      </div>
      <MDBBtn
        className='me-1'
        color='primary'
        onClick={handleToolExecution}
      >
        run
      </MDBBtn>
    </div>
  )
}

export default Playground