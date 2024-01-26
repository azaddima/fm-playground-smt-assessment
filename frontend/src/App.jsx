import React, {useState, useEffect} from 'react'
import {BrowserRouter as Router, Route, Routes} from 'react-router-dom'
import './assets/style/index.css'
import Nav from './components/Utils/Nav'
import Footer from './components/Utils/Footer'
import Playground from './components/Playground/Playground'
import Missing from './components/Utils/Missing'

// { id: "smt2",  value: "3", label: "SMT", short: "SMT" },

const App = () => {
    const [editorValue, setEditorValue] = useState('');
    const [language, setLanguage] = useState('');

    // eslint-disable-next-line no-unused-vars
    const handleEditorValueChange = (code) => {
        setEditorValue(code);
    };

    return (
        <div>
            <Nav
                setEditorValue={setEditorValue}
                setLanguage={setLanguage}
            />
            <Router>
                <Routes>
                    <Route path="/" element={
                        <Playground editorValue={editorValue}
                                    setEditorValue={setEditorValue}
                                    language={{id: "smt2", value: "3", label: "SMT", short: "SMT"}}
                                    setLanguage={setLanguage}/>}
                    />
                    <Route path="*" element={<Missing/>}/>
                </Routes>
            </Router>
            <Footer/>
        </div>
    )
}

export default App