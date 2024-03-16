import React, {useEffect, useState} from 'react'
import Editor from './Editor.jsx'
import {MDBBtn} from 'mdb-react-ui-kit';
import PlainOutput from './PlainOutput.jsx'
import {executeCmdTool} from '../../api/toolsApi.js'
import fileList from './fileNameList.json';


const Playground = ({editorValue, setEditorValue, language, setLanguage}) => {
    const [isExecuting, setIsExecuting] = useState(false);
    const [output, setOutput] = useState('') // contains the output of the tool
    const [currentTask, setCurrentTask] = useState("1");

    const handleToolExecution = async () => {
        setOutput('')
        try {
            setIsExecuting(true);

            executeCmdTool(editorValue)
                .then((res) => {
                    setOutput(res.result)
                    setIsExecuting(false);
                })
                .catch((err) => {
                    console.log(err)
                    setIsExecuting(false);
                })
        } catch (err) {
            console.log(err)
            setIsExecuting(false);
        }
    }

    useEffect(() => {
        console.log(currentTask);

        const loadFile = async (value) => {
            try {
                const response = await fetch(fileList[value]);
                if (!response.ok) {
                    throw new Error('Failed to load file');
                }
                return await response.text();
            } catch (error) {
                console.error('Error loading file:', error);
            }
        };

        // Call the loadFile function
        const text = loadFile(currentTask);
        text.then(result => {
            setEditorValue(result);
        })


    }, [currentTask]);


    /**
     * Update the output area with the code passed as a prop to the PlainOutput component.
     * @param {*} newCode
     */
    const handleOutputChange = (newCode) => {
        setOutput(newCode);
    };

    return (
        <div className="container mt-5 pt-5">
            <select value={currentTask} onChange={e => setCurrentTask(e.target.value)}>
                <option value={"1"}>Lecture 1</option>
                <option value={"3"}>Boolean Task</option>
                <option value={"4"}>Mathematics</option>
            </select>
            <div className="row">
                <div className="col-md-6" style={{backgroundColor: 'white'}}>
                    <div className='row'>
                        <div className='col-md-12 mx-auto mb-2'>
                            <div className='d-flex justify-content-between'>
                                <div className='col-md-4'>
                                    <h2>Input</h2>
                                </div>

                            </div>
                        </div>
                        <Editor
                            height='60vh'
                            setEditorValue={setEditorValue}
                            editorValue={editorValue}
                            language={language}
                            setLanguage={setLanguage}
                            theme='vs-dark'
                        />
                        <MDBBtn
                            className='mx-auto my-3'
                            style={{width: '95%'}}
                            color='primary'
                            onClick={handleToolExecution}
                            disabled={isExecuting}
                        >
                            {isExecuting ? 'Running...' : 'RUN'}
                        </MDBBtn>
                    </div>
                </div>
                <div className='col-md-6' style={{backgroundColor: 'white'}}>
                    <div className='row'>
                        <div className='col-md-12'>
                            <div className={`d-flex justify-content-between ${language.id !== 'xmv' ? 'mb-3' : ''}`}>
                                <h2>Output</h2>
                            </div>
                        </div>
                        <div className='col-md-12'>
                            <PlainOutput
                                code={output}
                                height='60vh'
                                onChange={handleOutputChange}/>
                        </div>
                    </div>
                </div>
            </div>
        </div>
    )
}


export default Playground