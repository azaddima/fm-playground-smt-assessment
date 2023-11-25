import React from 'react'
import { BrowserRouter as Router, Route, Routes } from 'react-router-dom'
import Nav from './components/Design/Nav'
import Footer from './components/Design/Footer'
import Playground from './components/Playground/Playground'
import Login from './components/Authentication/Login'


const App = () => {
  return (
    <div>
      <Nav/>
      <Router>
        <Routes>
          <Route path="/" element={<Playground />} />
          <Route path="/login" element={<Login />} />
        </Routes>
      </Router>
      <Footer/>
    </div>
  )
}

export default App